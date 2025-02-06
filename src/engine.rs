use std::cell::RefCell;
use std::iter::once;
use std::ops::Deref;
use std::ops::DerefMut;
use std::path::Path;
use std::rc::Rc;

use rhai::CustomType;
use rhai::{
    packages::{CorePackage, Package},
    Dynamic, Engine, EvalAltResult, Scope, Variant,
};

use crate::internal::ToBe;

/// A type alias for the result of script execution within the `FormattingEngine`.
///
/// This alias simplifies error handling when executing Rhai scripts, encapsulating
/// either a successful result (`T`) or an error (`Box<EvalAltResult>`).
///
/// # Examples
///
/// ```rust
/// use script_format::{
///     FormattingEngine,
///     ScriptResult,
/// };
///
/// fn execute_script(script: &str) -> ScriptResult<()> {
///     let mut engine = FormattingEngine::new(false);
///     engine.format("data", 42, script)?;
///     Ok(())
/// }
/// ```
///
/// # Type Parameters
///
/// * `T` - The type of the successful result.
pub type ScriptResult<T> = Result<T, Box<EvalAltResult>>;

/// A wrapper around the Rhai `Engine` for formatting data using a dsl based on rhai.
///
/// `FormattingEngine` allows you to register custom types and format them using a custom dsl based on rhai.
///
/// # Examples
///
/// ```rust
/// use script_format::FormattingEngine;
///
/// let mut engine = FormattingEngine::new(false);
/// let result = engine.format("name", "World", "- `Hello, ${name}!`");
/// assert_eq!(result.unwrap(), "Hello, World!");
/// ```
///
/// # Features
///
/// - Custom type registration
/// - Script execution with data binding
/// - Debug support for script evaluation
pub struct FormattingEngine {
    engine: Engine,
    messages: Rc<RefCell<Vec<String>>>,
}

impl Deref for FormattingEngine {
    type Target = Engine;

    fn deref(&self) -> &Self::Target {
        &self.engine
    }
}

impl DerefMut for FormattingEngine {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.engine
    }
}

impl FormattingEngine {
    fn register_value<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.engine
            .register_fn("++", move |a: T, b: serde_value::Value| {
                vec![a.to_string(), serde_json::to_string(&b).unwrap()]
            });
        self.engine
            .register_fn("++", move |a: serde_value::Value, b: T| {
                vec![serde_json::to_string(&a).unwrap(), b.to_string()]
            });
    }

    fn register_string_concat_void<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.engine
            .register_fn("++", move |a: T, _b: ()| vec![a.to_string()]);
        self.engine
            .register_fn("++", move |_a: (), b: T| vec![b.to_string()]);
    }

    fn register_string_concat<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.engine.register_fn("++", move |a: T, b: &str| {
            vec![a.to_string(), b.to_string()]
        });
        self.engine.register_fn("++", move |a: &str, b: T| {
            vec![a.to_string(), b.to_string()]
        });
        self.engine
            .register_fn("++", move |a: T, b: T| vec![a.to_string(), b.to_string()]);
    }

    fn register_string_concat_vec<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.engine.register_fn("++", move |a: Vec<T>, b: &str| {
            a.iter()
                .map(ToString::to_string)
                .chain(once(b.to_owned()))
                .collect::<Vec<_>>()
        });
        self.engine.register_fn("++", move |a: &str, b: Vec<T>| {
            b.iter()
                .map(ToString::to_string)
                .chain(once(a.to_owned()))
                .collect::<Vec<_>>()
        });
        self.engine.register_fn("++", move |a: Vec<T>, b: Vec<T>| {
            a.iter()
                .map(ToString::to_string)
                .chain(b.iter().map(ToString::to_string))
                .collect::<Vec<_>>()
        });
    }

    fn register_concat<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.register_string_concat::<T>();
        self.register_string_concat_vec::<T>();
        self.register_string_concat_void::<T>();
    }

    fn register_msg<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.register_msg_single::<T>();
        self.register_msg_multi::<T, &str>();
        self.register_msg_multi::<T, String>();
        self.register_msg_multi::<T, bool>();
        self.register_msg_multi::<T, i64>();
        self.register_msg_multi::<T, u64>();
        self.register_msg_multi::<T, i32>();
        self.register_msg_multi::<T, u32>();
        self.register_msg_multi::<T, i16>();
        self.register_msg_multi::<T, u16>();
        self.register_msg_multi::<T, i8>();
        self.register_msg_multi::<T, u8>();
        self.register_msg_multi::<T, usize>();
        self.register_msg_multi::<T, isize>();
        self.register_msg_multi::<T, i128>();
        self.register_msg_multi::<T, u128>();
        self.register_msg_multi::<T, f32>();
        self.register_msg_multi::<T, f64>();
    }

    fn register_msg_multi<
        A: Variant + Clone + std::fmt::Display,
        B: Variant + Clone + std::fmt::Display,
    >(
        &mut self,
    ) {
        self.engine
            .register_fn("++", move |a: A, b: B| vec![a.to_string(), b.to_string()]);

        self.engine
            .register_fn("++", move |b: B, a: A| vec![b.to_string(), a.to_string()]);

        self.engine.register_fn("++", move |a: Option<A>, b: B| {
            if let Some(a) = a {
                vec![a.to_string(), b.to_string()]
            } else {
                vec![b.to_string()]
            }
        });

        self.engine.register_fn("++", move |a: A, b: Option<B>| {
            if let Some(b) = b {
                vec![a.to_string(), b.to_string()]
            } else {
                vec![a.to_string()]
            }
        });

        self.engine
            .register_fn("++", move |a: Option<A>, b: Option<B>| match (a, b) {
                (Some(a), Some(b)) => vec![a.to_string(), b.to_string()],
                (Some(a), None) => vec![a.to_string()],
                (None, Some(b)) => vec![b.to_string()],
                (None, None) => vec![],
            });
    }

    fn register_msg_single<T: Variant + Clone + std::fmt::Display>(&mut self) {
        {
            let messages = self.clone_messages();
            self.engine.register_fn("-", move |msg: T| {
                messages.borrow_mut().push(msg.to_string());
            });
        }

        {
            let messages = self.clone_messages();
            self.engine.register_fn("-", move |msg: Option<T>| {
                if let Some(msg) = msg {
                    messages.borrow_mut().push(msg.to_string());
                }
            });
        }
    }

    fn register_vec<T: Variant + Clone>(&mut self) {
        self.engine
            .register_type::<Vec<T>>()
            .register_fn("len", |v: Vec<T>| v.len())
            .register_iterator::<Vec<T>>()
            .register_iterator::<&Vec<&T>>()
            .register_iterator::<Vec<T>>()
            .register_iterator::<&Vec<&T>>()
            .register_indexer_get(|v: &mut Vec<T>, i: i64| {
                v[usize::try_from(i).unwrap()].to_owned()
            });
    }

    fn register_vec_printable<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.engine.register_fn("++", move |a: Vec<T>| {
            a.iter().map(ToString::to_string).collect::<Vec<_>>()
        });

        self.register_vec_printable_single::<T, &str>();
        self.register_vec_printable_single::<T, String>();
        self.register_vec_printable_single::<T, bool>();
        self.register_vec_printable_single::<T, i64>();
        self.register_vec_printable_single::<T, u64>();
        self.register_vec_printable_single::<T, i32>();
        self.register_vec_printable_single::<T, u32>();
        self.register_vec_printable_single::<T, i16>();
        self.register_vec_printable_single::<T, u16>();
        self.register_vec_printable_single::<T, i8>();
        self.register_vec_printable_single::<T, u8>();
        self.register_vec_printable_single::<T, usize>();
        self.register_vec_printable_single::<T, isize>();
        self.register_vec_printable_single::<T, i128>();
        self.register_vec_printable_single::<T, u128>();
        self.register_vec_printable_single::<T, f32>();
        self.register_vec_printable_single::<T, f64>();

        self.register_vec_printable_multi::<T, &str>();
        self.register_vec_printable_multi::<T, String>();
        self.register_vec_printable_multi::<T, bool>();
        self.register_vec_printable_multi::<T, i64>();
        self.register_vec_printable_multi::<T, u64>();
        self.register_vec_printable_multi::<T, i32>();
        self.register_vec_printable_multi::<T, u32>();
        self.register_vec_printable_multi::<T, i16>();
        self.register_vec_printable_multi::<T, u16>();
        self.register_vec_printable_multi::<T, i8>();
        self.register_vec_printable_multi::<T, u8>();
        self.register_vec_printable_multi::<T, usize>();
        self.register_vec_printable_multi::<T, isize>();
        self.register_vec_printable_multi::<T, i128>();
        self.register_vec_printable_multi::<T, u128>();
        self.register_vec_printable_multi::<T, f32>();
        self.register_vec_printable_multi::<T, f64>();

        self.register_vec_printable_void::<&str>();
        self.register_vec_printable_void::<String>();
        self.register_vec_printable_void::<bool>();
        self.register_vec_printable_void::<i64>();
        self.register_vec_printable_void::<u64>();
        self.register_vec_printable_void::<i32>();
        self.register_vec_printable_void::<u32>();
        self.register_vec_printable_void::<i16>();
        self.register_vec_printable_void::<u16>();
        self.register_vec_printable_void::<i8>();
        self.register_vec_printable_void::<u8>();
        self.register_vec_printable_void::<usize>();
        self.register_vec_printable_void::<isize>();
        self.register_vec_printable_void::<i128>();
        self.register_vec_printable_void::<u128>();
        self.register_vec_printable_void::<f32>();
        self.register_vec_printable_void::<f64>();
    }

    fn register_vec_printable_void<T: Variant + Clone + std::fmt::Display>(&mut self) {
        self.engine.register_fn("++", move |a: Vec<T>, _b: ()| {
            a.iter().map(ToString::to_string).collect::<Vec<_>>()
        });
        self.engine.register_fn("++", move |_a: (), b: Vec<T>| {
            b.iter().map(ToString::to_string).collect::<Vec<_>>()
        });
        self.engine
            .register_fn("++", move |a: Option<Vec<T>>, _b: ()| {
                a.unwrap_or_default()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            });
        self.engine
            .register_fn("++", move |_a: (), b: Option<Vec<T>>| {
                b.unwrap_or_default()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            });
    }

    fn register_vec_printable_multi<
        A: Variant + Clone + std::fmt::Display,
        B: Variant + Clone + std::fmt::Display,
    >(
        &mut self,
    ) {
        self.engine.register_fn("++", move |a: Vec<A>, b: Vec<B>| {
            a.iter()
                .map(ToString::to_string)
                .chain(b.iter().map(ToString::to_string))
                .collect::<Vec<_>>()
        });

        self.engine
            .register_fn("++", move |a: Option<Vec<A>>, b: Vec<B>| {
                let a: Vec<A> = a.unwrap_or_default();
                a.iter()
                    .map(ToString::to_string)
                    .chain(b.iter().map(ToString::to_string))
                    .collect::<Vec<_>>()
            });
        self.engine
            .register_fn("++", move |a: Vec<A>, b: Option<Vec<B>>| {
                let b: Vec<B> = b.unwrap_or_default();
                a.iter()
                    .map(ToString::to_string)
                    .chain(b.iter().map(ToString::to_string))
                    .collect::<Vec<_>>()
            });
    }

    fn register_vec_printable_single<
        A: Variant + Clone + std::fmt::Display,
        B: Variant + Clone + std::fmt::Display,
    >(
        &mut self,
    ) {
        self.engine.register_fn("++", move |a: Vec<A>, b: B| {
            a.iter()
                .map(ToString::to_string)
                .chain(once(b.to_string()))
                .collect::<Vec<_>>()
        });
        self.engine.register_fn("++", move |a: A, b: Vec<B>| {
            once(a.to_string())
                .chain(b.iter().map(ToString::to_string))
                .collect::<Vec<_>>()
        });

        self.engine
            .register_fn("++", move |a: Option<Vec<A>>, b: B| {
                let a: Vec<A> = a.unwrap_or_default();
                a.iter()
                    .map(ToString::to_string)
                    .chain(once(b.to_string()))
                    .collect::<Vec<_>>()
            });
        self.engine
            .register_fn("++", move |a: A, b: Option<Vec<B>>| {
                let b: Vec<B> = b.unwrap_or_default();
                once(a.to_string())
                    .chain(b.iter().map(ToString::to_string))
                    .collect::<Vec<_>>()
            });

        self.engine
            .register_fn("++", move |a: Vec<A>, b: Option<B>| {
                let mut res = a.iter().map(ToString::to_string).collect::<Vec<_>>();
                if let Some(b) = b {
                    res.push(b.to_string());
                }
                res
            });
        self.engine
            .register_fn("++", move |a: Option<A>, b: Vec<B>| {
                a.iter()
                    .map(ToString::to_string)
                    .chain(b.iter().map(ToString::to_string))
                    .collect::<Vec<_>>()
            });
    }

    fn register_type_dynamic<T: Variant + Clone + 'static, C: From<T> + PartialEq + 'static>(
        &mut self,
        is_call: fn(&Dynamic) -> bool,
        as_call: fn(&Dynamic) -> Result<C, &'static str>,
    ) {
        self.engine
            .register_fn("any", move |arr: rhai::Array, v: T| {
                let value: C = v.into();
                arr.iter()
                    .filter(|a| is_call(a))
                    .map(|a| {
                        let a: C = as_call(&a).unwrap().into();
                        a
                    })
                    .filter(|a| *a == value)
                    .into_iter()
                    .count()
                    > 0
            });
        self.engine
            .register_fn("all", move |arr: rhai::Array, v: T| {
                let value: C = v.into();
                let expected = arr.len();
                arr.iter()
                    .filter(|a| is_call(a))
                    .map(|a| {
                        let a: C = as_call(&a).unwrap().into();
                        a
                    })
                    .filter(|a| *a == value)
                    .into_iter()
                    .count()
                    == expected
            });
        self.engine
            .register_fn("none", move |arr: rhai::Array, v: T| {
                let value: C = v.into();
                arr.iter()
                    .filter(|a| is_call(a))
                    .map(|a| {
                        let a: C = as_call(&a).unwrap().into();
                        a
                    })
                    .filter(|a| *a == value)
                    .into_iter()
                    .count()
                    == 0
            });
    }

    fn register_comparison<
        A: Variant + Clone + AsCast<C>,
        B: Variant + Clone + AsCast<C>,
        C: PartialEq + PartialOrd,
    >(
        &mut self,
    ) {
        self.engine
            .register_fn(">", |left: A, right: B| left.as_cast() > right.as_cast());
        self.engine
            .register_fn(">=", |left: A, right: B| left.as_cast() >= right.as_cast());
        self.engine
            .register_fn("<", |left: A, right: B| left.as_cast() < right.as_cast());
        self.engine
            .register_fn("<=", |left: A, right: B| left.as_cast() <= right.as_cast());
        self.engine
            .register_fn("!=", |left: A, right: B| left.as_cast() != right.as_cast());
        self.engine
            .register_fn("==", |left: A, right: B| left.as_cast() == right.as_cast());

        self.engine
            .register_fn(">", |left: B, right: A| left.as_cast() > right.as_cast());
        self.engine
            .register_fn(">=", |left: B, right: A| left.as_cast() >= right.as_cast());
        self.engine
            .register_fn("<", |left: B, right: A| left.as_cast() < right.as_cast());
        self.engine
            .register_fn("<=", |left: B, right: A| left.as_cast() <= right.as_cast());
        self.engine
            .register_fn("!=", |left: B, right: A| left.as_cast() != right.as_cast());
        self.engine
            .register_fn("==", |left: B, right: A| left.as_cast() == right.as_cast());
    }

    fn register_options<T: Variant + Clone>(&mut self) {
        self.engine
            .register_fn("is_some", crate::internal::script_is_some::<T>)
            .register_fn("unwrap", crate::internal::script_unwrap::<T>)
            .register_fn("unwrap_or", crate::internal::script_unwrap_or::<T>);
    }
}

impl FormattingEngine {
    /// Creates a new `FormattingEngine` instance.
    ///
    /// # Arguments
    ///
    /// * `debug` - A boolean indicating whether to enable debug functions inside Rhai.
    ///
    /// # Returns
    ///
    /// A new, pre-configured, `FormattingEngine` instance.
    #[must_use]
    pub fn new(debug: bool) -> Self {
        build_engine(debug)
    }

    /// Registers a custom type with the Rhai engine.
    ///
    /// This method also registers the `is_some`, `unwrap`, and `unwrap_or` methods for the custom type,
    /// as well as the necessary functions for using the type inside a `Vec<T>`.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The type to register, which must implement `Variant` and `Clone`.
    ///
    /// # Returns
    ///
    /// A mutable reference to `self` to allow method chaining.
    pub fn register_type<T: Variant + Clone>(&mut self) -> &mut Self {
        self.engine.register_type::<T>();
        self.register_vec::<T>();
        self.register_options::<T>();

        self
    }

    /// Makes a custom type comparable.
    ///
    /// This method also registers the `any`, `none` and `all` methods for the custom type,
    /// as well as the necessary functions for using the type inside a `Vec<T>`.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The type to register, which must implement `Variant` and `Clone`.
    ///
    /// # Returns
    ///
    /// A mutable reference to `self` to allow method chaining.
    pub fn make_comparable<T: Variant + PartialEq + Clone>(&mut self) -> &mut Self {
        self.register_type::<T>();
        self.register_options::<T>();
        self.register_vec::<T>();
        self.register_fn("any", crate::internal::script_any_type::<T>)
            .register_fn("all", crate::internal::script_all_type::<T>)
            .register_fn("none", crate::internal::script_none_type::<T>);
        self
    }

    /// Builds and registers a custom type with the Rhai engine.
    ///
    /// This function initializes the custom type using `build_type` and then registers it
    /// with the Rhai engine, making it accessible within the DSL scripts.
    ///
    /// # Type Parameters
    ///
    /// * `T` - The custom type to build and register, which must implement `Variant`, `CustomType`, and `Clone`.
    ///
    /// # Returns
    ///
    /// A mutable reference to `self` to allow method chaining.
    ///
    /// # Example
    ///
    /// ```rust
    /// use script_format::{
    ///     rhai::{CustomType, TypeBuilder},
    ///     FormattingEngine,
    /// };
    ///
    /// #[derive(Clone, CustomType)]
    /// struct Person {
    ///     name: String,
    ///     age: i32,
    /// }
    ///
    /// let mut engine = FormattingEngine::new(false);
    /// engine.build_type::<Person>();
    /// ```
    pub fn build_type<T: Variant + CustomType + Clone>(&mut self) -> &mut Self {
        self.engine.build_type::<T>();
        self.register_type::<T>();
        self
    }

    /// Runs the formatting script with the provided scope.
    ///
    /// Use the scope to pass data to the script.
    /// **You must register (`build_type` / `register_type`) each custom type that should be accessed beforehand so that rhai can properly access it.**
    ///
    /// # Arguments
    ///
    /// * `scope` - The Rhai `Scope` to be used during script evaluation.
    /// * `script` - The script to execute for formatting.
    ///
    /// # Errors
    ///
    /// Returns an error if script execution fails.
    ///
    /// # Returns
    ///
    /// A formatted string result.
    pub fn format_with_scope(&mut self, scope: &mut Scope, script: &str) -> ScriptResult<String> {
        scope.push_constant("NL", "\n");

        self.messages.borrow_mut().clear();
        let mut new_script = Vec::new();
        let mut line = String::new();
        let mut is_line_start = true;
        for c in script.chars() {
            if c == ';' {
                is_line_start = true;
            } else if c == '\n' {
                if is_line_start
                    && !line.trim().starts_with("-")
                    && (line.contains("++")
                        || line.contains("then_emit")
                        || line.contains("or_emit"))
                {
                    line = format!("- {}", line);
                }
                is_line_start = false;
                new_script.push(line);
                line = String::new();
            } else {
                line.push(c);
            }
        }
        self.engine.run_with_scope(scope, script)?;

        Ok(self.messages.borrow().join(""))
    }

    /// Formats an object using a script from a file with the provided scope.
    ///
    /// Use the scope to pass data to the script.
    /// **You must register (`build_type` / `register_type`) each custom type that should be accessed beforehand so that rhai can properly access it.**
    ///
    /// # Arguments
    ///
    /// * `scope` - The Rhai `Scope` to be used during script evaluation.
    /// * `script` - The file path of the script to execute.
    ///
    /// # Errors
    ///
    /// Returns an error if file reading or script execution fails.
    ///
    /// # Returns
    ///
    /// A formatted string result.
    #[cfg(not(feature = "web"))]
    pub fn format_from_file_with_scope<P: AsRef<Path>>(
        &mut self,
        scope: &mut Scope,
        script: P,
    ) -> ScriptResult<String> {
        match std::fs::read_to_string(script.as_ref()) {
            Ok(script) => self.format_with_scope(scope, &script),
            Err(e) => Err(e.to_string().into()),
        }
    }

    /// Clones the messages buffer.
    ///
    /// This can be useful if you want to register a custom function that needs to access the messages buffer.
    ///
    /// # Returns
    ///
    /// A reference-counted pointer to the messages buffer.
    pub fn clone_messages(&self) -> Rc<RefCell<Vec<String>>> {
        self.messages.clone()
    }

    /// Formats an object using a script.
    ///
    /// **You must register (`build_type` / `register_type`) each custom type that should be accessed beforehand so that rhai can properly access it.**
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the data variable in the script.
    /// * `data` - The data object to format.
    /// * `script` - The script to execute for formatting.
    ///
    /// # Errors
    ///
    /// Returns an error if script execution fails.
    ///
    /// # Returns
    ///
    /// A formatted string result.
    pub fn format<T: Variant + Clone>(
        &mut self,
        name: &str,
        data: T,
        script: &str,
    ) -> ScriptResult<String> {
        self.register_type::<T>();

        let mut scope = Scope::new();
        scope.push_constant(name, data);

        self.format_with_scope(&mut scope, script)
    }

    /// Formats an object using a script from a file.
    ///
    /// **You must register (`build_type` / `register_type`) each custom type that should be accessed beforehand so that rhai can properly access it.**
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the data variable in the script.
    /// * `data` - The data object to format.
    /// * `script` - The file path of the script to execute.
    ///
    /// # Errors
    ///
    /// Returns an error if file reading or script execution fails.
    ///
    /// # Returns
    ///
    /// A formatted string result.
    #[cfg(not(feature = "web"))]
    pub fn format_from_file<T: Variant + Clone, P: AsRef<Path>>(
        &mut self,
        name: &str,
        data: T,
        script: P,
    ) -> ScriptResult<String> {
        match std::fs::read_to_string(script.as_ref()) {
            Ok(script) => self.format(name, data, &script),
            Err(e) => Err(e.to_string().into()),
        }
    }
}

#[allow(clippy::too_many_lines)]
fn build_engine(debug: bool) -> FormattingEngine {
    let mut engine = FormattingEngine::new(debug);
    engine.set_max_expr_depths(128, 64);

    let package = CorePackage::new();

    engine.register_global_module(package.as_shared_module());

    let indent = Rc::new(RefCell::new("    ".to_owned()));

    {
        let indent = indent.clone();

        // This isn't deprecated, the api is just volatile and may change
        #[allow(deprecated)]
        engine.on_var(move |name, _, _| match name {
            "IND" => Ok(Some(indent.borrow().clone().into())),
            _ => Ok(None),
        });
    }

    {
        let indent = indent.clone();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        engine.register_fn("IND", move |count: i64| {
            indent.borrow().repeat(count as usize)
        });
    }

    {
        let indent = indent.clone();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        engine.register_fn("SET_INDENT", move |value: &str| {
            value.clone_into(&mut indent.borrow_mut());
        });
    }

    {
        let indent = indent.clone();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        engine.register_fn("SET_INDENT", move |value: &str, count: i64| {
            *indent.borrow_mut() = value.repeat(count as usize)
        });
    }

    {
        let indent = indent.clone();
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        engine.register_fn("SET_INDENT", move |count: i64| {
            *indent.borrow_mut() = " ".repeat(count as usize)
        });
    }

    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    engine.register_fn("NL", |count: i64| "\n".repeat(count as usize));

    engine.register_iterator::<Vec<serde_value::Value>>();

    engine.register_options::<&str>();
    engine.register_options::<String>();
    engine.register_options::<bool>();
    engine.register_options::<i64>();
    engine.register_options::<u64>();
    engine.register_options::<i32>();
    engine.register_options::<u32>();
    engine.register_options::<i16>();
    engine.register_options::<u16>();
    engine.register_options::<i8>();
    engine.register_options::<u8>();
    engine.register_options::<usize>();
    engine.register_options::<isize>();
    engine.register_options::<i128>();
    engine.register_options::<u128>();
    engine.register_options::<f32>();
    engine.register_options::<f64>();

    engine.register_type_dynamic::<i8, i64>(Dynamic::is_int, Dynamic::as_int);
    engine.register_type_dynamic::<i16, i64>(Dynamic::is_int, Dynamic::as_int);
    engine.register_type_dynamic::<i32, i64>(Dynamic::is_int, Dynamic::as_int);
    engine.register_type_dynamic::<i64, i64>(Dynamic::is_int, Dynamic::as_int);

    engine.register_type_dynamic::<u8, i64>(Dynamic::is_int, Dynamic::as_int);
    engine.register_type_dynamic::<u16, i64>(Dynamic::is_int, Dynamic::as_int);
    engine.register_type_dynamic::<u32, i64>(Dynamic::is_int, Dynamic::as_int);

    engine.register_type_dynamic::<f32, f64>(Dynamic::is_float, Dynamic::as_float);
    engine.register_type_dynamic::<f64, f64>(Dynamic::is_float, Dynamic::as_float);

    engine.register_type_dynamic::<bool, bool>(Dynamic::is_bool, Dynamic::as_bool);

    fn dynamic_as_string(dynamic: &Dynamic) -> Result<String, &'static str> {
        dynamic.to_owned().into_string()
    }

    engine.register_type_dynamic::<String, String>(Dynamic::is_string, dynamic_as_string);
    engine.register_type_dynamic::<&str, String>(Dynamic::is_string, dynamic_as_string);

    engine
        .register_fn("join", crate::internal::script_join)
        .register_fn("split", crate::internal::script_split)
        .register_fn("splitn", crate::internal::script_splitn)
        .register_fn("rsplitn", crate::internal::script_rsplitn)
        .register_fn("is_empty", crate::internal::script_string_is_empty)
        .register_fn("is_empty", crate::internal::script_array_is_empty)
        .register_fn("starts_with", crate::internal::script_starts_with)
        .register_fn("ends_with", crate::internal::script_ends_with)
        .register_fn("trim", crate::internal::script_trim)
        .register_fn("is_string", crate::internal::script_is_no_string)
        .register_fn("is_string", crate::internal::script_is_string);

    // DSL
    engine.build_type::<ToBe>();
    engine
        .register_custom_operator("zip", 65)
        .unwrap()
        .register_custom_operator("to_be", 60)
        .unwrap()
        .register_custom_operator("and", 60)
        .unwrap()
        .register_fn("and", |a: bool, b: bool| a && b)
        .register_custom_operator("or", 30)
        .unwrap()
        .register_fn("or", |a: bool, b: bool| a || b)
        .register_custom_operator("xor", 30)
        .unwrap()
        .register_fn("xor", |a: bool, b: bool| a ^ b)
        .register_custom_operator("contains", 25)
        .unwrap()
        .register_custom_operator("equals", 25)
        .unwrap()
        .register_custom_operator("require", 25)
        .unwrap()
        .register_custom_operator("any", 25)
        .unwrap()
        .register_custom_operator("all", 25)
        .unwrap()
        .register_custom_operator("none", 25)
        .unwrap()
        .register_fn("contains", crate::internal::script_map_contains)
        .register_fn("contains", crate::internal::script_string_contains)
        .register_fn("equals", crate::internal::script_map_equals)
        .register_fn("equals", crate::internal::script_value_equals)
        .register_fn("equals", crate::internal::script_array_equals)
        .register_fn("contains", crate::internal::script_array_contains)
        .register_fn("require", crate::internal::script_require)
        .register_fn("to_be", crate::internal::script_to_be)
        .register_fn("any", crate::internal::script_any)
        .register_fn("any", crate::internal::script_any_void)
        .register_fn("all", crate::internal::script_all)
        .register_fn("all", crate::internal::script_all_void)
        .register_fn("none", crate::internal::script_none)
        .register_fn("none", crate::internal::script_none_void);

    engine.register_msg_single::<&str>();
    engine.register_msg_single::<String>();
    engine.register_msg_single::<bool>();
    engine.register_msg_single::<i64>();
    engine.register_msg_single::<u64>();
    engine.register_msg_single::<i32>();
    engine.register_msg_single::<u32>();
    engine.register_msg_single::<i16>();
    engine.register_msg_single::<u16>();
    engine.register_msg_single::<i8>();
    engine.register_msg_single::<u8>();
    engine.register_msg_single::<usize>();
    engine.register_msg_single::<isize>();
    engine.register_msg_single::<i128>();
    engine.register_msg_single::<u128>();
    engine.register_msg_single::<f32>();
    engine.register_msg_single::<f64>();

    engine.register_msg::<&str>();
    engine.register_msg::<String>();
    engine.register_msg::<bool>();
    engine.register_msg::<i64>();
    engine.register_msg::<u64>();
    engine.register_msg::<i32>();
    engine.register_msg::<u32>();
    engine.register_msg::<i16>();
    engine.register_msg::<u16>();
    engine.register_msg::<i8>();
    engine.register_msg::<u8>();
    engine.register_msg::<usize>();
    engine.register_msg::<isize>();
    engine.register_msg::<i128>();
    engine.register_msg::<u128>();
    engine.register_msg::<f32>();
    engine.register_msg::<f64>();

    engine.register_comparison::<u8, u8, u8>();
    engine.register_comparison::<u8, u16, u16>();
    engine.register_comparison::<u8, u32, u32>();
    engine.register_comparison::<u8, u64, u64>();
    engine.register_comparison::<u8, usize, u128>();
    engine.register_comparison::<u8, u128, u128>();

    engine.register_comparison::<u16, u16, u16>();
    engine.register_comparison::<u16, u32, u32>();
    engine.register_comparison::<u16, u64, u64>();
    engine.register_comparison::<u16, usize, u128>();
    engine.register_comparison::<u16, u128, u128>();

    engine.register_comparison::<u32, u32, u32>();
    engine.register_comparison::<u32, u64, u64>();
    engine.register_comparison::<u32, usize, u128>();
    engine.register_comparison::<u32, u128, u128>();

    engine.register_comparison::<u64, u64, u64>();
    engine.register_comparison::<u64, usize, u128>();
    engine.register_comparison::<u64, u128, u128>();

    engine.register_comparison::<usize, usize, u128>();
    engine.register_comparison::<usize, u128, u128>();

    engine.register_comparison::<u128, u128, u128>();

    engine.register_comparison::<i8, i8, i8>();
    engine.register_comparison::<i8, i16, i16>();
    engine.register_comparison::<i8, i32, i32>();
    engine.register_comparison::<i8, i64, i64>();
    engine.register_comparison::<i8, isize, i128>();
    engine.register_comparison::<i8, i128, i128>();

    engine.register_comparison::<i16, i16, i16>();
    engine.register_comparison::<i16, i32, i32>();
    engine.register_comparison::<i16, i64, i64>();
    engine.register_comparison::<i8, isize, i128>();
    engine.register_comparison::<i16, i128, i128>();

    engine.register_comparison::<i32, i32, i32>();
    engine.register_comparison::<i32, i64, i64>();
    engine.register_comparison::<i32, isize, i128>();
    engine.register_comparison::<i32, i128, i128>();

    engine.register_comparison::<i64, i64, i64>();
    engine.register_comparison::<i64, isize, i128>();
    engine.register_comparison::<i64, i128, i128>();

    engine.register_comparison::<isize, isize, i128>();
    engine.register_comparison::<isize, i128, i128>();

    engine.register_comparison::<i128, i128, i128>();

    engine.register_comparison::<f32, f32, f32>();
    engine.register_comparison::<f32, f64, f64>();

    engine.register_comparison::<u8, f32, f32>();
    engine.register_comparison::<u16, f32, f32>();
    engine.register_comparison::<u32, f64, f64>();

    engine.register_comparison::<i8, f32, f32>();
    engine.register_comparison::<i16, f32, f32>();
    engine.register_comparison::<i32, f64, f64>();

    engine.register_value::<&str>();
    engine.register_value::<String>();
    engine.register_value::<bool>();
    engine.register_value::<i64>();
    engine.register_value::<u64>();
    engine.register_value::<i32>();
    engine.register_value::<u32>();
    engine.register_value::<i16>();
    engine.register_value::<u16>();
    engine.register_value::<i8>();
    engine.register_value::<u8>();
    engine.register_value::<usize>();
    engine.register_value::<isize>();
    engine.register_value::<i128>();
    engine.register_value::<u128>();
    engine.register_value::<f32>();
    engine.register_value::<f64>();

    fn dynamic_to_string(value: Dynamic) -> ScriptResult<String> {
        if value.is_string() {
            Ok(value.into_string()?)
        } else if value.is_char() {
            Ok(value.as_char().as_ref().map(ToString::to_string)?)
        } else if value.is_int() {
            Ok(value.as_int().as_ref().map(ToString::to_string)?)
        } else if value.is_float() {
            Ok(value.as_float().as_ref().map(ToString::to_string)?)
        } else if value.is_bool() {
            Ok(value.as_bool().as_ref().map(ToString::to_string)?)
        } else {
            Err(format!("Unsupported type: {}", value.type_name()).into())
        }
    }

    {
        let messages = engine.clone_messages();
        engine.register_fn("-", move |msg: Dynamic| -> ScriptResult<()> {
            if msg.is_array() {
                let arr = msg.into_array().unwrap();
                for m in arr {
                    messages.borrow_mut().push(dynamic_to_string(m)?);
                }
            } else {
                messages.borrow_mut().push(dynamic_to_string(msg)?);
            }
            Ok(())
        });
    }

    {
        let messages = engine.clone_messages();
        engine.register_fn("-", move |msg: serde_value::Value| {
            messages
                .borrow_mut()
                .push(serde_json::to_string(&msg).unwrap());
        });
    }

    engine.register_fn("++", move |a: serde_value::Value, b: serde_value::Value| {
        vec![
            serde_json::to_string(&a).unwrap(),
            serde_json::to_string(&b).unwrap(),
        ]
    });

    engine.register_concat::<&str>();
    engine.register_concat::<String>();
    engine.register_concat::<bool>();
    engine.register_concat::<i64>();
    engine.register_concat::<u64>();
    engine.register_concat::<i32>();
    engine.register_concat::<u32>();
    engine.register_concat::<i16>();
    engine.register_concat::<u16>();
    engine.register_concat::<i8>();
    engine.register_concat::<u8>();
    engine.register_concat::<usize>();
    engine.register_concat::<isize>();
    engine.register_concat::<i128>();
    engine.register_concat::<u128>();
    engine.register_concat::<f32>();
    engine.register_concat::<f64>();

    engine.register_vec_printable::<&str>();
    engine.register_vec_printable::<String>();
    engine.register_vec_printable::<bool>();
    engine.register_vec_printable::<i64>();
    engine.register_vec_printable::<u64>();
    engine.register_vec_printable::<i32>();
    engine.register_vec_printable::<u32>();
    engine.register_vec_printable::<i16>();
    engine.register_vec_printable::<u16>();
    engine.register_vec_printable::<i8>();
    engine.register_vec_printable::<u8>();
    engine.register_vec_printable::<usize>();
    engine.register_vec_printable::<isize>();
    engine.register_vec_printable::<i128>();
    engine.register_vec_printable::<u128>();
    engine.register_vec_printable::<f32>();
    engine.register_vec_printable::<f64>();

    engine.register_vec::<()>();

    engine
        .register_fn("any", crate::internal::script_any_type::<bool>)
        .register_fn("all", crate::internal::script_any_type::<bool>)
        .register_fn("none", crate::internal::script_any_type::<bool>)
        .register_fn("++", move |(): (), b: &str| vec![b.to_owned()])
        .register_fn("++", move |(): (), b: usize| vec![b.to_string()])
        .register_custom_operator("++", 15)
        .unwrap()
        .register_custom_operator("then_emit", 20)
        .unwrap()
        .register_fn(
            "then_emit",
            move |a: bool, msg: &str| {
                if a {
                    Some(msg.to_owned())
                } else {
                    None
                }
            },
        )
        .register_custom_operator("or_emit", 20)
        .unwrap()
        .register_fn(
            "or_emit",
            move |a: bool, msg: &str| {
                if !a {
                    Some(msg.to_owned())
                } else {
                    None
                }
            },
        );
    // END DSL

    if debug {
        engine.on_print(move |x| eprintln!("INFO => {x}"));
        engine.on_debug(move |x, _, pos| eprintln!("DEBUG({pos:?}) => {x}"));
    } else {
        engine.on_print(|_| ());
        engine.on_debug(|_, _, _| ());
    }

    engine.disable_symbol("eval");

    engine
}

macro_rules! impl_as_cast {
    ($A: ty, ($($B: ty),*)) => {
        $(
            impl AsCast<$B> for $A {
                fn as_cast(self) -> $B {
                    self as $B
                }
            }
        )*
    }
}

trait AsCast<T> {
    fn as_cast(self) -> T;
}

impl_as_cast!(u8, (u8, u16, u32, u64, u128, usize));
impl_as_cast!(i8, (i8, i16, i32, i64, i128, isize));

impl_as_cast!(u16, (u16, u32, u64, u128, usize));
impl_as_cast!(i16, (i16, i32, i64, i128, isize));

impl_as_cast!(u32, (u32, u64, u128, usize));
impl_as_cast!(i32, (i32, i64, i128, isize));

impl_as_cast!(u64, (u64, u128));
impl_as_cast!(i64, (i64, i128));

impl_as_cast!(usize, (usize, u128));
impl_as_cast!(isize, (isize, i128));

impl_as_cast!(u128, (u128));
impl_as_cast!(i128, (i128));

impl_as_cast!(f32, (f32, f64));
impl_as_cast!(f64, (f64));

impl_as_cast!(u8, (f32, f64));
impl_as_cast!(u16, (f32, f64));
impl_as_cast!(u32, (f64));

impl_as_cast!(i8, (f32, f64));
impl_as_cast!(i16, (f32, f64));
impl_as_cast!(i32, (f64));
