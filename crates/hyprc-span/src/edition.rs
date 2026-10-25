#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum Edition {
    E2015,
    E2018,
    E2021,
    E2024,
}

impl Edition {
    pub fn parse(s: &str) -> Option<Edition> {
        Some(match s {
            "2015" => Edition::E2015,
            "2018" => Edition::E2018,
            "2021" => Edition::E2021,
            "2024" => Edition::E2024,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Edition::E2015 => "2015",
            Edition::E2018 => "2018",
            Edition::E2021 => "2021",
            Edition::E2024 => "2024",
        }
    }

    pub fn at_least_2018(self) -> bool {
        self >= Edition::E2018
    }
}
