fn formatting_macros(name: &str, mut output: impl std::io::Write) {
    print!("hello {}", name);
    println!("hello {}", name);
    eprint!("hello {}", name);
    eprintln!("hello {}", name);
    let _text = format!("hello {}", name);
    let _ = write!(output, "hello {}", name);
    let _ = writeln!(output, "hello {}", name);
}
