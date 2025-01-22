# Script Format

I regularly needed to output data in a custom format, which is why I created a DSL based on [Rhai](https://rhai.rs/book/).

## DSL
The most important part of the DSL is the `++` operator.

The `++` operator takes the values to its left and right and stores them internally. Once the script is done running,
all the stored values get concatenated and returned.

This allows for a really nice way to express what should get output:
```rs
let some_number = 1;

// will output 'Test 1'
"Test " ++ some_number;
```

There are also a two more conveniences, namely `NL` and `IND`.

- `NL` is a constant holding the newline character (`\r`).
- `IND` is a constant holding the indentation string (Default: four spaces).

Theres also functions with the same name that take a number and return the value that amount of time. So if you want to
indent something by 3 levels, you can just write `IND(3)`.

## Quick Start
In order to use the DSL you need create a `FormattingEngine` and register all types you want to work with.

After that, you can just call the appropriate format function to format your data.