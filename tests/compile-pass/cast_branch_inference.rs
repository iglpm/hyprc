fn cast_after_branch(level: i32) -> usize {
    (if level > 10 { 10 } else { level }) as usize
}
