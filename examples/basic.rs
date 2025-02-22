use script_format::{
    // The crate re-exports the Rhai engine for convenience
    rhai::{CustomType, TypeBuilder},
    FormattingEngine,
};

// Derive the `CustomType` trait to enable Rhai to access the fields of the struct
#[derive(Clone, CustomType)]
struct Person {
    pub name: String,
    pub age: i32,
}

fn main() {
    // Create a new `FormattingEngine` instance with debug mode disabled
    let mut engine = FormattingEngine::new(false);
    // Register the custom type so the Rhai engine can access it
    engine.build_type::<Person>();

    let person = Person {
        name: "Alice".into(),
        age: 30,
    };

    let script = r#"
SET_INDENT(".. ");                         // sets the current indent string to ".. "
~ "Person Details:";                       // - emits a single message
~ NL;                                      // NL emits a newline
~ IND ++ "Name: " ++ person.name ++ NL;    // ++ emits the message and concatenates it

// custom operator then_emit emits a message conditionally
~ IND(2) ++ person.name contains "Alice" then_emit "- Hello Alice" ++ NL;

~ IND ++ "Age: " ++ person.age ++ NL;      // ++ automatically converts the values to strings
~ IND(2);                                  // custom operator IND indents the message
person.age > 18 then_emit "- Adult" ++ NL; // custom operator then_emit emits a message conditionally

[1, 2, 3] contains 2 then_emit "- Contains 2" ++ NL;
[1, 2, 3] any 2 then_emit "- Some values are 2" ++ NL;
[1, 2, 3] all 2 then_emit "- All values are 2" ++ NL;
[1, 2, 3] none 2 then_emit "- No 2 found" ++ NL;
"#;

    let expected = r#"
Person Details:
.. Name: Alice
.. .. - Hello Alice
.. Age: 30
.. .. - Adult
- Contains 2
- Some values are 2
    "#
    .trim();

    // Execute the Rhai script to format the person's details
    let result = engine.format("person", person, script);
    assert_eq!(result.unwrap(), expected);
}
