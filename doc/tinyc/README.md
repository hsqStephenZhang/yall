# tinyc

## Overview

tinyc is a lightweight parser for a simplified version of the C programming language. It is designed to demonstrate the principles of parsing and compiling, providing a foundation for understanding language processing. The project includes a lexer, parser, and an Abstract Syntax Tree (AST) representation of the parsed code.

## Features

- Lexer: Tokenizes input source code into meaningful tokens.
- Parser: Constructs an AST from the token stream based on the defined grammar.
- AST: Represents the structure of the parsed code for further processing or analysis.
- Example Programs: Includes example TinyC programs to demonstrate syntax and functionality.

## Project Structure

```
tinyc
├── src
│   ├── main.rs        # Entry point of the application
│   ├── lib.rs         # Library code for the tinyc parser
│   ├── ast.rs         # Abstract Syntax Tree definitions
│   ├── lexer.rs       # Lexer implementation
│   ├── parser.rs      # Parser implementation
│   ├── tinyc.yapg     # Grammar definition for tinyc
│   └── tests
│       ├── mod.rs     # Test module for organizing tests
│       └── parser_tests.rs # Unit tests for the parser
├── examples
│   ├── simple.tc      # Example of a simple tinyc program
│   └── fibonacci.tc   # Example of a Fibonacci sequence implementation
├── Cargo.toml         # Project configuration file
└── README.md          # Documentation for the tinyc project
```

## Building the Project

To build the tinyc project, ensure you have Rust and Cargo installed. Then, navigate to the project directory and run:

```
cargo build
```

## Running the Parser

To run the tinyc parser, use the following command:

```
cargo run -- <path_to_tinyc_file>
```

Replace `<path_to_tinyc_file>` with the path to the TinyC source file you wish to parse.

## Examples

### Simple Program

The `examples/simple.tc` file contains a simple TinyC program that demonstrates basic syntax.

### Fibonacci Program

The `examples/fibonacci.tc` file showcases a more complex implementation of the Fibonacci sequence in TinyC.

## Contributing

Contributions are welcome! Please feel free to submit issues or pull requests to improve the tinyc project.

## License

This project is licensed under the MIT License. See the LICENSE file for more details.