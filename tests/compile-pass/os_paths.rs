fn os_strings_and_paths(value: &std::ffi::OsString, path: &std::path::PathBuf) {
    let _is_disabled = value == "0";
    let _in_system_root = path.starts_with("/usr");
}
