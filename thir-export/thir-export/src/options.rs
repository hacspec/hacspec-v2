use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum Glob {
    One,  // *
    Many, // **
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum NamespaceChunk {
    Glob(Glob),
    Exact(String),
}

impl std::convert::From<&str> for NamespaceChunk {
    fn from(s: &str) -> Self {
        match s {
            "*" => NamespaceChunk::Glob(Glob::One),
            "**" => NamespaceChunk::Glob(Glob::Many),
            _ => NamespaceChunk::Exact(String::from(s)),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct Namespace{
    pub chunks: Vec<NamespaceChunk>
}

impl std::convert::From<String> for Namespace {
    fn from(s: String) -> Self {
        Namespace {
            chunks: s.split("::")
                .into_iter()
                .filter(|s| s.len() > 0)
                .map(|s| NamespaceChunk::from(s))
                .collect(),
        }
    }
}

impl Namespace {
    pub fn matches(&self, path: &Vec<String>) -> bool {
        fn aux(pattern: &[NamespaceChunk], path: &[String]) -> bool {
            match (pattern, path) {
                ([], []) => true,
                ([NamespaceChunk::Exact(x), pattern @ ..], [y, path @ ..]) => {
                    x == y && aux(pattern, path)
                }
                ([NamespaceChunk::Glob(Glob::One), pattern @ ..], [_, path @ ..]) => {
                    aux(pattern, path)
                }
                ([NamespaceChunk::Glob(Glob::Many), pattern @ ..], []) => aux(pattern, path),
                ([NamespaceChunk::Glob(Glob::Many), pattern_tl @ ..], [path_hd, path_tl @ ..]) => {
                    aux(pattern_tl, path) || aux(pattern, path_tl)
                }
                _ => false,
            }
        }
        aux(self.chunks.as_slice(), path.as_slice())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub enum PathOrDash {
    Dash,
    Path(PathBuf),
}

impl std::convert::From<&std::ffi::OsStr> for PathOrDash {
    fn from(s: &std::ffi::OsStr) -> Self {
        if s == "-" {
            PathOrDash::Dash
        } else {
            PathOrDash::Path(PathBuf::from(s))
        }
    }
}

impl PathOrDash {
    pub fn open_or_stdout(&self) -> Box<dyn std::io::Write> {
        match self {
            PathOrDash::Dash => box std::io::stdout(),
            PathOrDash::Path(path) => box std::fs::File::create(&path).unwrap(),
        }
    }
    pub fn map_path<F: FnOnce(&Path) -> PathBuf>(&self, f: F) -> Self {
        match self {
            PathOrDash::Path(path) => PathOrDash::Path(f(path)),
            PathOrDash::Dash => PathOrDash::Dash,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ForceCargoBuild {
    data: u128,
}

impl std::convert::From<&std::ffi::OsStr> for ForceCargoBuild {
    fn from(s: &std::ffi::OsStr) -> Self {
        ForceCargoBuild {
            data: if s == "false" {
                use std::time::{SystemTime, UNIX_EPOCH};
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|r| r.as_millis())
                    .unwrap_or(0)
            } else {
                0
            },
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Options {
    pub output_file: PathOrDash,
    pub inline_macro_calls: Vec<Namespace>,
    pub export_json_schema: Option<PathOrDash>,
    pub cargo_flags: Vec<String>,
}
