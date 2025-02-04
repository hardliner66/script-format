//! Simple DSL for formatting data based on Rhai.
//!
//! This crate provides a custom DSL built on top of the Rhai scripting engine,
//! designed specifically for formatting data. The DSL introduces a set of custom
//! functions and operators to enhance the capabilities of Rhai when it comes to
//! text formatting tasks.
//!
//! # Key Features
//!
//! - **Custom Operators:** Extended with operators like `++`, `and`, `or`, `xor`,
//!   `contains`, `equals`, `require`, `then_emit`, and `or_emit` for expressive scripts.
//! - **Message Emission:** Use `-` to emit a single message and `++` to emit multiple messages.
//! - **Conditional Emission:** The `then_emit` and `or_emit` operators allow conditional message emission
//!   based on boolean conditions.
//! - **Indentation Control:** `IND` and `SET_INDENT` functions to manage indentation dynamically.
//! - **Flexible Data Handling:** Supports arrays, maps, strings, and custom types.
//! - **Shortcuts:** `IND` and `NL` constants can be used as shortcuts for `IND(1)` and `NL(1)` respectively.
//!
//! # DSL Overview
//!
//! - `- <message>`: Emits a message.
//! - `<a> ++ <b>`: Emits messages `a` and `b`.
//! - `then_emit(<condition>, <message>)`: Emits `<message>` if `<condition>` is true.
//! - `or_emit(<condition>, <message>)`: Emits `<message>` if `<condition>` is false.
//! - `SET_INDENT(<string>)`: Sets the current indent string.
//! - `IND(<count>)`: Generates indentation with the current indent string.
//! - `NL(<count>)`: Inserts newlines.
//! - `IND`: Shortcut for `IND(1)`.
//! - `NL`: Shortcut for `NL(1)`.
//!
//! # DSL Example
//!
//! We're going to use the following script to format a person's details:
//! ```rhai
#![doc = include_str!("../doc_test.rhai")]
//! ```
//!
//! ```rust
//! use script_format::{
//!     // The crate re-exports the Rhai engine for convenience
//!     rhai::{CustomType, TypeBuilder},
//!     FormattingEngine,
//! };
//!
//! // Derive the `CustomType` trait to enable Rhai to access the fields of the struct
//! #[derive(Clone, CustomType)]
//! struct Person {
//!     pub name: String,
//!     pub age: i32,
//! }
//!
//! // Create a new `FormattingEngine` instance with debug mode disabled
//! let mut engine = FormattingEngine::new(false);
//! // Register the custom type so the Rhai engine can access it
//! engine.build_type::<Person>();
//!
//! let person = Person {
//!     name: "Alice".into(),
//!     age: 30,
//! };
//!
//! let script = r#"
#![doc = include_str!("../doc_test.rhai")]
//! "#;
//!
//! let expected = r#"
//! Person Details:
//! .. Name: Alice
//! .. Age: 30
//! .. .. - Adult
//!     "#
//!     .trim();
//!
//! // Execute the Rhai script to format the person's details
//! let result = engine.format("person", person, script);
//! assert_eq!(result.unwrap(), expected);
//! ```
//!
//! **Expected Output:**
//! ```txt
//! Name: Alice
//! Age: 30 - Adult
//! ```
//!
//! This DSL is ideal for generating formatted text dynamically based on data inputs.

use std::cell::RefCell;
use std::ops::Deref;
use std::ops::DerefMut;
use std::path::Path;
use std::rc::Rc;

use rhai::CustomType;
use rhai::{
    packages::{CorePackage, Package},
    Engine, EvalAltResult, Map, Scope, Variant,
};

mod internal;

pub use rhai;

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
            .register_indexer_get(|v: &mut Vec<$T>, i: i64| v[usize::try_from(i).unwrap()].clone());
        )*
    };
}

macro_rules! register_options {
    ($engine: expr, ($($T: ty),*)) => {
        $(
        $engine
            .register_fn("is_some", internal::script_is_some::<$T>)
            .register_fn("unwrap", internal::script_unwrap::<$T>)
            .register_fn("unwrap_or", internal::script_unwrap_or::<$T>);
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
        self.engine.register_type::<T>();
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
        scope.push_constant("NL", "\n");

        self.messages.borrow_mut().clear();
        self.engine
            .run_file_with_scope(scope, script.as_ref().to_path_buf())?;

        Ok(self.messages.borrow().join(""))
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
    pub fn format(
        &mut self,
        name: &str,
        data: impl Variant + Clone,
        script: &str,
    ) -> ScriptResult<String> {
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
    pub fn format_from_file<P: AsRef<Path>>(
        &mut self,
        name: &str,
        data: impl Variant + Clone,
        script: P,
    ) -> ScriptResult<String> {
        let mut scope = Scope::new();
        scope.push_constant(name, data);

        self.format_from_file_with_scope(&mut scope, script)
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
        (String, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128)
    );

    engine
        .register_fn("join", internal::script_join)
        .register_fn("split", internal::script_split)
        .register_fn("splitn", internal::script_splitn)
        .register_fn("rsplitn", internal::script_rsplitn)
        .register_fn("is_empty", internal::script_string_is_empty)
        .register_fn("is_empty", internal::script_array_is_empty)
        .register_fn("starts_with", internal::script_starts_with)
        .register_fn("ends_with", internal::script_ends_with)
        .register_fn("trim", internal::script_trim)
        .register_fn("is_string", internal::script_is_no_string)
        .register_fn("is_string", internal::script_is_string);

    // DSL
    engine
        .register_custom_operator("and", 60)
        .unwrap()
        .register_fn("and", |a: bool, b: bool| a && b)
        .register_custom_operator("or", 30)
        .unwrap()
        .register_fn("or", |a: bool, b: bool| a || b)
        .register_custom_operator("xor", 30)
        .unwrap()
        .register_fn("xor", |a: bool, b: bool| a ^ b)
        .register_custom_operator("contains", 15)
        .unwrap()
        .register_custom_operator("equals", 15)
        .unwrap()
        .register_custom_operator("require", 15)
        .unwrap()
        .register_fn("contains", internal::script_map_contains)
        .register_fn("contains", internal::script_string_contains)
        .register_fn("equals", internal::script_map_equals)
        .register_fn("equals", internal::script_value_equals)
        .register_fn("equals", internal::script_array_equals)
        .register_fn("contains", internal::script_array_contains)
        .register_fn("require", internal::script_require)
        .register_fn("any", internal::script_any)
        .register_fn("all", internal::script_all)
        .register_fn("none", internal::script_none);

    macro_rules! register_msg_single {
        ($($T: ty),*) => {
            $(
            {
                let messages = messages.clone();
                engine.register_fn("-", move |msg: $T| {
                    messages.borrow_mut().push(format!("{msg}"));
                });
            }
            )*
        };
    }

    register_msg_single!(&str, usize, bool);

    macro_rules! register_msg_multi {
        ($(($A: ty, $B: ty)),*) => {
            $(
            {
                let messages = messages.clone();
                engine.register_fn("++", move |a: $A, b: $B| {
                    messages.borrow_mut().push(format!("{a}"));
                    messages.borrow_mut().push(format!("{b}"));
                });
            }
            )*
        };
    }

    register_msg_multi!(
        (&str, &str),
        (&str, usize),
        (usize, &str),
        (usize, usize),
        (&str, bool),
        (bool, &str),
        (bool, usize),
        (bool, bool)
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
                let messages = messages.clone();
                engine.register_fn("++", move |a: $A, b: serde_value::Value| {
                    messages.borrow_mut().push(format!("{a}"));
                    messages
                        .borrow_mut()
                        .push(serde_json::to_string(&b).unwrap());
                });
            }
            )*
        };
    }

    macro_rules! register_value_left {
        ($($B: ty),*) => {
            $(
            {
                let messages = messages.clone();
                engine.register_fn("++", move |a: serde_value::Value, b: $B| {
                    messages
                        .borrow_mut()
                        .push(serde_json::to_string(&a).unwrap());
                    messages.borrow_mut().push(format!("{b}"));
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

    {
        let messages = messages.clone();
        engine.register_fn("-", move |msg: serde_value::Value| {
            messages
                .borrow_mut()
                .push(serde_json::to_string(&msg).unwrap());
        });
    }

    register_value!(
        &str, String, char, bool, i64, u64, i32, u32, i16, u16, i8, u8, usize, isize, i128, u128
    );

    {
        let messages = messages.clone();
        engine.register_fn("++", move |a: serde_value::Value, b: serde_value::Value| {
            messages
                .borrow_mut()
                .push(serde_json::to_string(&a).unwrap());
            messages
                .borrow_mut()
                .push(serde_json::to_string(&b).unwrap());
        });
    }

    macro_rules! register_string_concat_void {
        ($($T: ty),*) => {$({
            let messages = messages.clone();
            engine.register_fn("++", move |a: $T, _b: ()| {
                messages.borrow_mut().push(a.to_string());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |_a: (), b: $T| {
                messages.borrow_mut().push(b.to_string());
            });
        }
        )*};
    }

    macro_rules! register_string_concat {
        ($($T: ty),*) => {$({
            let messages = messages.clone();
            engine.register_fn("++", move |a: $T, b: &str| {
                messages.borrow_mut().push(a.to_string());
                messages.borrow_mut().push(b.to_owned());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: &str, b: $T| {
                messages.borrow_mut().push(a.to_owned());
                messages.borrow_mut().push(b.to_string());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: $T, b: $T| {
                messages.borrow_mut().push(a.to_string());
                messages.borrow_mut().push(b.to_string());
            });
        })*};
    }

    macro_rules! register_string_concat_vec {
        ($($T: ty),*) => {$({
            let messages = messages.clone();
            engine.register_fn("++", move |a: &Vec<$T>, b: &str| {
                messages.borrow_mut().push(format!("{:?}", a));
                messages.borrow_mut().push(b.to_owned());
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: &str, b: &Vec<$T>| {
                messages.borrow_mut().push(a.to_owned());
                messages.borrow_mut().push(format!("{:?}", b));
            });
        }
        {
            let messages = messages.clone();
            engine.register_fn("++", move |a: &Vec<$T>, b: &Vec<$T>| {
                messages.borrow_mut().push(format!("{:?}", a));
                messages.borrow_mut().push(format!("{:?}", b));
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

    register_concat!(i32, u32, i64, u64, f32, f64, bool);

    {
        let messages = messages.clone();
        engine.register_fn("++", move |(): (), b: &str| {
            messages.borrow_mut().push(b.to_owned());
        });
    }
    {
        let messages = messages.clone();
        engine.register_fn("++", move |(): (), b: usize| {
            messages.borrow_mut().push(b.to_string());
        });
    }
    engine.register_custom_operator("++", 15).unwrap();
    {
        let messages = messages.clone();
        engine.register_fn("emit", move |msg: &str| {
            messages.borrow_mut().push(msg.to_owned());
        });
    }
    engine.register_custom_operator("then_emit", 15).unwrap();
    {
        let messages = messages.clone();
        engine.register_fn("then_emit", move |a: bool, msg: &str| {
            if a {
                messages.borrow_mut().push(msg.to_owned());
            }
            a
        });
    }
    {
        let messages = messages.clone();
        engine.register_fn("then_emit", move |a: bool, m: Map| {
            if a {
                let msg = m
                    .get("msg")
                    .map(|e| e.clone().into_string().unwrap())
                    .unwrap();
                messages.borrow_mut().push(msg);
            }
            a
        });
    }
    engine.register_custom_operator("or_emit", 15).unwrap();
    {
        let messages = messages.clone();
        engine.register_fn("or_emit", move |a: bool, msg: &str| {
            if !a {
                messages.borrow_mut().push(msg.to_owned());
            }
            a
        });
    }
    {
        engine.register_fn("or_emit", move |a: bool, m: Map| {
            if !a {
                let msg = m
                    .get("msg")
                    .map(|e| e.clone().into_string().unwrap())
                    .unwrap();
                messages.borrow_mut().push(msg);
            }
            a
        });
    }
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
