fn main() {
    let grammar_files = ["src/expr.yapg", "src/list.yapg"];

    // 1. Tell Cargo to watch this file.
    // If this file hasn't changed, Cargo will skip running this build.rs entirely.
    for grammar_file in &grammar_files {
        println!("cargo:rerun-if-changed={}", grammar_file);
    }

    // 2. Run your generator
    let mut config = yapg::generator::Configuration::new();
    for grammar_file in grammar_files {
        config = config.add_grammar_file(grammar_file);
    }
    config.build().expect("Failed to build grammar");
}
