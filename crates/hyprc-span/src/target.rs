//! Targets: what the compiler generates code for, and the `cfg` values that describe it.

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Arch {
    X86_64,
    Aarch64,
    X86,
    Arm,
    Riscv64,
    Other,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Endian {
    Little,
    Big,
}

#[derive(Clone, Debug)]
pub struct Target {
    pub triple: String,
    pub arch: Arch,
    /// `target_arch`
    pub arch_name: String,
    pub os: String,
    pub env: String,
    pub vendor: String,
    pub abi: String,
    /// `unix`, `windows`, `wasm`, or empty.
    pub families: Vec<String>,
    pub pointer_width: u32,
    pub endian: Endian,
    /// `target_feature`s enabled by default.
    pub features: Vec<String>,
    /// Widths with atomic operations (`target_has_atomic`): "8", "16", "32", "64", "ptr".
    pub atomic_widths: Vec<String>,
    pub executables: bool,
}

impl Target {
    /// The target of the machine hyprc runs on.
    pub fn host() -> Target {
        let triple = match (std::env::consts::ARCH, std::env::consts::OS) {
            ("x86_64", "linux") => "x86_64-unknown-linux-gnu",
            ("aarch64", "linux") => "aarch64-unknown-linux-gnu",
            ("aarch64", "macos") => "aarch64-apple-darwin",
            ("x86_64", "macos") => "x86_64-apple-darwin",
            ("x86_64", "windows") => "x86_64-pc-windows-msvc",
            ("aarch64", "windows") => "aarch64-pc-windows-msvc",
            _ => "x86_64-unknown-linux-gnu",
        };
        Target::from_triple(triple).expect("the host target is known")
    }

    /// Fills a target in from its triple: `arch-vendor-os[-env]`.
    pub fn from_triple(triple: &str) -> Option<Target> {
        let parts: Vec<&str> = triple.split('-').collect();
        if parts.len() < 2 {
            return None;
        }
        let arch_part = parts[0];
        let (arch, arch_name, pointer_width, endian) = match arch_part {
            "x86_64" => (Arch::X86_64, "x86_64", 64, Endian::Little),
            "aarch64" | "arm64" => (Arch::Aarch64, "aarch64", 64, Endian::Little),
            "i686" | "i586" | "i386" => (Arch::X86, "x86", 32, Endian::Little),
            a if a.starts_with("arm") || a.starts_with("thumb") => {
                (Arch::Arm, "arm", 32, Endian::Little)
            }
            "riscv64gc" | "riscv64" | "riscv64imac" => {
                (Arch::Riscv64, "riscv64", 64, Endian::Little)
            }
            _ => (Arch::Other, arch_part, 64, Endian::Little),
        };
        let (vendor, rest) = if parts.len() >= 3 {
            (parts[1], &parts[2..])
        } else {
            ("unknown", &parts[1..])
        };
        let os = match rest.first().copied() {
            Some("linux") => "linux",
            Some("darwin") => "macos",
            Some("windows") => "windows",
            Some("freebsd") => "freebsd",
            Some("none") => "none",
            Some(other) => other,
            None => "none",
        };
        let env = rest.get(1).map_or("", |e| match *e {
            e if e.starts_with("gnu") => "gnu",
            e if e.starts_with("musl") => "musl",
            "msvc" => "msvc",
            other => other,
        });
        let abi = rest.get(1).map_or("", |e| match *e {
            "gnueabihf" | "musleabihf" => "eabihf",
            "gnueabi" | "musleabi" => "eabi",
            _ => "",
        });
        let families = match os {
            "linux" | "macos" | "freebsd" | "android" | "ios" | "netbsd" | "openbsd" => {
                vec!["unix".to_string()]
            }
            "windows" => vec!["windows".to_string()],
            _ => Vec::new(),
        };
        let features: Vec<String> = match arch {
            // The x86-64 baseline (`x86-64` CPU).
            Arch::X86_64 => ["fxsr", "sse", "sse2", "x87"]
                .iter()
                .map(|s| s.to_string())
                .collect(),
            Arch::Aarch64 => ["neon"].iter().map(|s| s.to_string()).collect(),
            _ => Vec::new(),
        };
        let atomic_widths: Vec<String> = if pointer_width == 64 {
            ["8", "16", "32", "64", "ptr"]
                .iter()
                .map(|s| s.to_string())
                .collect()
        } else {
            ["8", "16", "32", "ptr"]
                .iter()
                .map(|s| s.to_string())
                .collect()
        };
        Some(Target {
            triple: triple.to_string(),
            arch,
            arch_name: arch_name.to_string(),
            os: os.to_string(),
            env: env.to_string(),
            vendor: vendor.to_string(),
            abi: abi.to_string(),
            families,
            pointer_width,
            endian,
            features,
            atomic_widths,
            executables: os != "none",
        })
    }

    pub fn is_unix(&self) -> bool {
        self.families.iter().any(|f| f == "unix")
    }
}
