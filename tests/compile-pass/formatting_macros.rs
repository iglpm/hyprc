fn formatting_macros(name: &str, mut output: impl std::io::Write) {
    print!("hello {}", name);
    println!("hello {}", name);
    eprint!("hello {}", name);
    eprintln!("hello {}", name);
    let _text = format!("hello {}", name);
    let _ = write!(output, "hello {}", name);
    let _ = writeln!(output, "hello {}", name);
}

macro_rules! expression_block_followed_by_a_statement {
    ($body:expr) => {{
        $body
        let answer = 42;
        answer
    }};
}

fn macro_expression_fragments_keep_block_boundaries() {
    let _: i32 = expression_block_followed_by_a_statement!({});
}
