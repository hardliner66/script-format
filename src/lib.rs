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
//! - **Value/Text Emission:** Use `~` to emit a single value
//! - **Concatenate multiple values:** Use `++` to stringify and concatenate multiple values.
//! - **Conditional Emission:** The `then_emit` and `or_emit` operators allow conditional value emission
//!   based on boolean conditions.
//! - **Indentation Control:** `IND` and `SET_INDENT` functions to manage indentation dynamically.
//! - **Flexible Data Handling:** Supports vector, maps, strings, and custom types.
//! - **Shortcuts:** `IND` and `NL` constants can be used as shortcuts for `IND(1)` and `NL(1)` respectively.
//!
//! # DSL Overview
//!
//! - `~ <value>`: Emits a value.
//! - `<a> ++ <b>`: Concatenates values `a` and `b`.
//! - `<condition> then_emit <value>`: Returns `<value>` if `<condition>` is true.
//! - `<condition> or_emit <value>`: Returns `<value>` if `<condition>` is false.
//! - `SET_INDENT(<string>)`: Sets the current indent string.
//! - `IND(<count>)`: Returns the currently set indent string for `<count>` times.
//! - `NL(<count>)`: Returns `<count>` newlines.
//! - `IND`: Shortcut for `IND(1)`.
//! - `NL`: Shortcut for `NL(1)`.
//! - `<vector> require <number> to_be <value>`: Throws an error if not exactly `<number>` of <value> are found.
//! - `<a> contains <b>`: Checks if `<a>` is part of `<b>`.
//! - `<value> equals <value>`: Checks if two maps are equal.
//! - `<vector> any <value>`: Checks if any of the values in `<vector>` is equal to `<value>`.
//! - `<vector> all <value>`: Checks if all of the values in `<vector>` are equal to `<value>`.
//! - `<vector> none <value>`: Checks if none of the values in `<vector>` are equal to `<value>`.
//! - `<a> and <b>`: Logical AND operation.
//! - `<a> or <b>`: Logical OR operation.
//! - `<a> xor <b>`: Logical XOR operation.
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

mod engine;
mod internal;

pub use rhai;

pub use crate::engine::{FormattingEngine, ScriptResult};
