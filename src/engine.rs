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

// macro_rules! basic_types {
//     () => {
//         &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
//         f64
//     }
// }

macro_rules! register_vec_printable_single {
    ($engine: expr, $A: ty, ($($B: ty),*)) => {
        $(
        {
            $engine
                .register_fn("++", move |a: Vec<$A>, b: $B| {
                    a.iter().map(|msg| format!("{msg}")).chain(once(format!("{b}"))).collect::<Vec<_>>()
                });
            $engine
                .register_fn("++", move |a: $A, b: Vec<$B>| {
                    once(format!("{a}")).chain(b.iter().map(|msg| format!("{msg}"))).collect::<Vec<_>>()
                });

            $engine
                .register_fn("++", move |a: Option<Vec<$A>>, b: $B| {
                    let a: Vec<$A> = a.unwrap_or_default();
                    a.iter()
                     .map(ToString::to_string).chain(once(b.to_string()))
                     .collect::<Vec<_>>()
                });
            $engine
                .register_fn("++", move |a: $A, b: Option<Vec<$B>>| {
                    let b: Vec<$B> = b.unwrap_or_default();
                    once(format!("{a}"))
                        .chain(b.iter().map(ToString::to_string))
                        .collect::<Vec<_>>()
                });

            $engine
                .register_fn("++", move |a: Vec<$A>, b: Option<$B>| {
                    let mut res = a.iter().map(ToString::to_string).collect::<Vec<_>>();
                    if let Some(b) = b {
                        res.push(b.to_string());
                    }
                    res
                });
            $engine
                .register_fn("++", move |a: Option<$A>, b: Vec<$B>| {
                    a.iter()
                     .map(|a| a.to_string())
                     .chain(b.iter().map(ToString::to_string))
                     .collect::<Vec<_>>()
                });
        }
        )*
    };
}

macro_rules! register_vec_printable_multi {
    ($engine: expr, $A: ty, ($($B: ty),*)) => {
        $(
        {
            $engine
            .register_fn("++", move |a: Vec<$A>, b: Vec<$B>| {
                a.iter().map(|msg| format!("{msg}")).chain(b.iter().map(|msg| format!("{msg}"))).collect::<Vec<_>>()
            });

            $engine
                .register_fn("++", move |a: Option<Vec<$A>>, b: Vec<$B>| {
                    let a: Vec<$A> = a.unwrap_or_default();
                    a.iter()
                     .map(ToString::to_string).chain(b.iter().map(ToString::to_string))
                     .collect::<Vec<_>>()
                });
            $engine
                .register_fn("++", move |a: Vec<$A>, b: Option<Vec<$B>>| {
                    let b: Vec<$B> = b.unwrap_or_default();
                    a.iter()
                     .map(ToString::to_string).chain(b.iter().map(ToString::to_string))
                     .collect::<Vec<_>>()
                });
        }
        )*
    };
}

macro_rules! register_vec_printable_void {
    ($engine: expr, ($($T: ty),*)) => {
    $(
    {
        $engine.register_fn("++", move |a: Vec<$T>, _b: ()| {
            a.iter().map(|msg| format!("{msg}")).collect::<Vec<_>>()
        });
    }
    {
        $engine.register_fn("++", move |_a: (), b: Vec<$T>| {
            b.iter().map(|msg| format!("{msg}")).collect::<Vec<_>>()
        });
    }
    {
        $engine.register_fn("++", move |a: Option<Vec<$T>>, _b: ()| {
            a.unwrap_or_default().iter().map(|msg| format!("{msg}")).collect::<Vec<_>>()
        });
    }
    {
        $engine.register_fn("++", move |_a: (), b: Option<Vec<$T>>| {
            b.unwrap_or_default().iter().map(|msg| format!("{msg}")).collect::<Vec<_>>()
        });
    }
    )*};
}

macro_rules! register_vec_printable {
    ($engine: expr, ($($T: ty),*)) => {
        $(
        {
            $engine.register_fn("++",move  |a: Vec<$T>| {
                a.iter().map(|msg| format!("{msg}")).collect::<Vec<_>>()
            });
        }


        register_vec_printable_single!($engine, $T, (
            &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
            f64
        ));

        register_vec_printable_multi!($engine, $T, (
            &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
            f64
        ));

        register_vec_printable_void!($engine, (
            &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
            f64
        ));
        )*
    };
}

macro_rules! register_vec {
    ($engine: expr, ($($T: ty),*)) => {
        $(
        $engine
            .register_type::<Vec<$T>>()
            .register_fn("len", |v: Vec<$T>| v.len())
            .register_iterator::<Vec<$T>>()
            .register_iterator::<&Vec<&$T>>()
            .register_iterator::<Vec<$T>>()
            .register_iterator::<&Vec<&$T>>()
            .register_indexer_get(|v: &mut Vec<$T>, i: i64| v[usize::try_from(i).unwrap()].to_owned());
        )*
    };
}

macro_rules! register_options {
    ($engine: expr, ($($T: ty),*)) => {
        $(
        $engine
            .register_fn("is_some", crate::internal::script_is_some::<$T>)
            .register_fn("unwrap", crate::internal::script_unwrap::<$T>)
            .register_fn("unwrap_or", crate::internal::script_unwrap_or::<$T>);
        )*
    };
}

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
fn register_type_dynamic<T: Clone + 'static, C: From<T> + PartialEq + 'static>(
    engine: &mut Engine,
    is_call: fn(&Dynamic) -> bool,
    as_call: fn(&Dynamic) -> Result<C, &'static str>,
) {
    engine.register_fn("any", move |arr: rhai::Array, v: T| {
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
    engine.register_fn("all", move |arr: rhai::Array, v: T| {
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
    engine.register_fn("none", move |arr: rhai::Array, v: T| {
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
        let messages = Rc::new(RefCell::new(Vec::new()));
        let engine = build_engine(messages.clone(), debug);
        Self { engine, messages }
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
        register_options!(self.engine, (T));
        register_vec!(self.engine, (T));

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
        self.engine.register_type::<T>();
        register_options!(self.engine, (T));
        register_vec!(self.engine, (T));
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
            Err(e) => Err(format!("{e}").into()),
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
            Err(e) => Err(format!("{e}").into()),
        }
    }
}

#[allow(clippy::too_many_lines)]
fn build_engine(messages: Rc<RefCell<Vec<String>>>, debug: bool) -> Engine {
    let mut engine = Engine::new();
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

    register_options!(
        engine,
        (
            &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128,
            f32, f64
        )
    );

    register_type_dynamic::<i8, i64>(&mut engine, Dynamic::is_int, Dynamic::as_int);
    register_type_dynamic::<i64, i64>(&mut engine, Dynamic::is_int, Dynamic::as_int);

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

    macro_rules! register_msg_single {
        ($($T: ty),*) => {
            $(
            {
                let messages = messages.clone();
                engine.register_fn("-", move |msg: $T| {
                    messages.borrow_mut().push(format!("{msg}"));
                });
            }

            {
                let messages = messages.clone();
                engine.register_fn("-", move |msg: Option<$T>| {
                    if let Some(msg) = msg {
                        messages.borrow_mut().push(format!("{msg}"));
                    }
                });
            }
            )*
        };
    }

    register_msg_single!(
        &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
        f64
    );

    macro_rules! register_msg_multi {
        ($A: ty, ($($B: ty),*)) => {
            $(
            {
                engine.register_fn("++", move |a: $A, b: $B| {
                    vec![
                        format!("{a}"),
                        format!("{b}"),
                    ]
                });
            }

            {
                engine.register_fn("++", move |b: $B, a: $A| {
                    vec![
                        format!("{b}"),
                        format!("{a}"),
                    ]
                });
            }

            {
                engine.register_fn("++", move |a: Option<$A>, b: $B| {
                    if let Some(a) = a {
                        vec![
                            format!("{a}"),
                            format!("{b}"),
                        ]
                    } else {
                        vec![
                            format!("{b}"),
                        ]
                    }
                });
            }

            {
                engine.register_fn("++", move |a: $A, b: Option<$B>| {
                    if let Some(b) = b {
                        vec![
                            format!("{a}"),
                            format!("{b}"),
                        ]
                    } else {
                        vec![
                            format!("{a}"),
                        ]
                    }
                });
            }

            {
                engine.register_fn("++", move |a: Option<$A>, b: Option<$B>| {
                    match (a, b) {
                        (Some(a), Some(b)) => vec![format!("{a}"), format!("{b}")],
                        (Some(a), None) => vec![format!("{a}")],
                        (None, Some(b)) => vec![format!("{b}")],
                        (None, None) => vec![],
                    }
                });
            }
            )*
        };
    }

    macro_rules! register_msg {
        ($($T: ty),*) => {
            $(
                register_msg_single!($T);
                register_msg_multi!($T,
                    (&str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32, f64
                    )
                );
            )*
        }
    }

    register_msg!(
        &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
        f64
    );

    macro_rules! register_comparison {
        ($(($A: ty, $B: ty, $C: ty)),*) => {
            $(
            engine.register_fn(">",  |left: $A, right: $B| (left as $C) >  (right as $C));
            engine.register_fn(">=", |left: $A, right: $B| (left as $C) >= (right as $C));
            engine.register_fn("<",  |left: $A, right: $B| (left as $C) <  (right as $C));
            engine.register_fn("<=", |left: $A, right: $B| (left as $C) <= (right as $C));
            engine.register_fn("!=", |left: $A, right: $B| (left as $C) != (right as $C));
            engine.register_fn("==", |left: $A, right: $B| (left as $C) == (right as $C));

            engine.register_fn(">",  |left: $B, right: $A| (left as $C) >  (right as $C));
            engine.register_fn(">=", |left: $B, right: $A| (left as $C) >= (right as $C));
            engine.register_fn("<",  |left: $B, right: $A| (left as $C) <  (right as $C));
            engine.register_fn("<=", |left: $B, right: $A| (left as $C) <= (right as $C));
            engine.register_fn("!=", |left: $B, right: $A| (left as $C) != (right as $C));
            engine.register_fn("==", |left: $B, right: $A| (left as $C) == (right as $C));

            )*
        };
    }

    register_comparison!(
        (u8, u16, u16),
        (u8, u32, u32),
        (u8, u64, u64),
        (u16, u32, u32),
        (u16, u64, u64),
        (u32, u64, u64),
        (i8, i16, i16),
        (i8, i32, i32),
        (i8, i64, i64),
        (i16, i32, i32),
        (i16, i64, i64),
        (i32, i64, i64),
        (i64, usize, i128),
        (i32, usize, i128),
        (i16, usize, i128),
        (i8, usize, i128),
        (u64, usize, usize),
        (u32, usize, usize),
        (u16, usize, usize),
        (u8, usize, usize),
        (f32, f64, f64)
    );

    macro_rules! register_value_right {
        ($($A: ty),*) => {
            $(
            {
                engine.register_fn("++", move |a: $A, b: serde_value::Value| {
                    vec![
                        format!("{a}"),
                        serde_json::to_string(&b).unwrap()
                    ]
                });
            }
            )*
        };
    }

    macro_rules! register_value_left {
        ($($B: ty),*) => {
            $(
            {
                engine.register_fn("++", move |a: serde_value::Value, b: $B| {
                    vec![
                        serde_json::to_string(&a).unwrap(),
                        format!("{b}")
                    ]
                });
            }
            )*
        };
    }

    macro_rules! register_value {
        ($($T: ty),*) => {
            $(
            register_value_left!($T);
            register_value_right!($T);
            )*
        };
    }

    fn dynamic_to_string(value: Dynamic) -> ScriptResult<String> {
        if value.is_string() {
            Ok(value.into_string()?)
        } else if value.is_char() {
            Ok(value.as_char().map(|b| b.to_string())?)
        } else if value.is_int() {
            Ok(value.as_int().map(|b| b.to_string())?)
        } else if value.is_float() {
            Ok(value.as_float().map(|b| b.to_string())?)
        } else if value.is_bool() {
            Ok(value.as_bool().map(|b| b.to_string())?)
        } else {
            Err(format!("Unsupported type: {}", value.type_name()).into())
        }
    }

    {
        let messages = messages.clone();
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
        let messages = messages.clone();
        engine.register_fn("-", move |msg: serde_value::Value| {
            messages
                .borrow_mut()
                .push(serde_json::to_string(&msg).unwrap());
        });
    }

    register_value!(
        &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
        f64
    );

    engine.register_fn("++", move |a: serde_value::Value, b: serde_value::Value| {
        vec![
            serde_json::to_string(&a).unwrap(),
            serde_json::to_string(&b).unwrap(),
        ]
    });

    macro_rules! register_string_concat_void {
        ($($T: ty),*) => {$({
            engine.register_fn("++", move |a: $T, _b: ()| {
                vec![
                    format!("{a}"),
                ]
            });
        }
        {
            engine.register_fn("++", move |_a: (), b: $T| {
                vec![
                    format!("{b}"),
                ]
            });
        }
        )*};
    }

    macro_rules! register_string_concat {
        ($($T: ty),*) => {$({
            engine.register_fn("++", move |a: $T, b: &str| {
                vec![
                    format!("{a}"),
                    format!("{b}")
                ]
            });
        }
        {
            engine.register_fn("++", move |a: &str, b: $T| {
                vec![
                    format!("{a}"),
                    format!("{b}")
                ]
            });
        }
        {
            engine.register_fn("++", move |a: $T, b: $T| {
                vec![
                    format!("{a}"),
                    format!("{b}")
                ]
            });
        })*};
    }

    macro_rules! register_string_concat_vec {
        ($($T: ty),*) => {$({
            engine.register_fn("++", move |a: Vec<$T>, b: &str| {
                a.iter().map(|m| format!("{m}")).chain(once(b.to_owned())).collect::<Vec<_>>()
            });
        }
        {
            engine.register_fn("++", move |a: &str, b: Vec<$T>| {
                b.iter().map(|m| format!("{m}")).chain(once(a.to_owned())).collect::<Vec<_>>()
            });
        }
        {
            engine.register_fn("++", move |a: Vec<$T>, b: Vec<$T>| {
                a.iter().map(|m| format!("{m}")).chain(b.iter().map(|m| format!("{m}"))).collect::<Vec<_>>()
            });
        })*};
    }

    macro_rules! register_concat {
        ($($T: ty),*) => {{
            register_string_concat!($($T),*);
            register_string_concat_vec!($($T),*);
            register_string_concat_void!($($T),*);
        }};
    }

    register_concat!(
        &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128, f32,
        f64
    );
    register_vec_printable!(
        engine,
        (
            &str, String, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128,
            f32, f64
        )
    );

    register_vec!(engine, (()));

    engine
        .register_fn("any", crate::internal::script_any_type::<bool>)
        .register_fn("all", crate::internal::script_any_type::<bool>)
        .register_fn("none", crate::internal::script_any_type::<bool>)
        .register_fn("++", move |(): (), b: &str| vec![b.to_owned()])
        .register_fn("++", move |(): (), b: usize| vec![format!("{b}")])
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
