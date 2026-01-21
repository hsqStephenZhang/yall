fn main() {
    let grammar_file = "src/datalog.yapg";
    println!("cargo:rerun-if-changed={}", grammar_file);

    yapg::generator::Configuration::new()
        .add_grammar_file(grammar_file)
        .build()
        .expect("Failed to build grammar");
}
