fn main() {
    let grammar_file = "src/calculator.yapg";

    // 1. Tell Cargo to watch this file.
    // If this file hasn't changed, Cargo will skip running this build.rs entirely.
    println!("cargo:rerun-if-changed={}", grammar_file);

    // 2. Run your generator
    yapg::generator::Configuration::new()
        .add_grammar_file(grammar_file)
        .build()
        .expect("Failed to build grammar");
}
