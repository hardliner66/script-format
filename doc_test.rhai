SET_INDENT(".. ");                        // sets the current indent string to ".. "
~ "Person Details:";                      // ~ emits a single message
~ NL;                                     // NL emits a newline
~ IND ++ "Name: " ++ person.name ++ NL;   // ++ concatenates the values
~ IND ++ "Age: " ++ person.age ++ NL;     // ++ automatically converts the values to strings
~ IND(2);                                 // custom operator IND indents the message
~ person.age > 18 then_emit("- Adult");   // custom operator then_emit emits a message conditionally