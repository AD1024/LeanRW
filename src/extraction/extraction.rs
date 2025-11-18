use anyhow::Result;
use libloading::Library;
use serde::Serialize;
use tree_sitter::{ffi::TSLanguage, Language, Parser};

/// Keep the `Library` alive as long as you use the `Language`.
struct LoadedLanguage {
    _lib: Library,      // must be kept, or the code is unloaded
    lang: Language,
}

unsafe fn load_lean_language(path: &str) -> anyhow::Result<LoadedLanguage> {
    // Load the shared object at runtime
    let lib = Library::new(path)?;

    // Symbol type: extern "C" fn() -> *const TSLanguage
    let lang_fn: libloading::Symbol<unsafe extern "C" fn() -> *const TSLanguage> =
        lib.get(b"tree_sitter_lean")?;

    let raw = lang_fn();
    let lang = Language::from_raw(raw);

    Ok(LoadedLanguage { _lib: lib, lang })
}

#[derive(Debug, Serialize)]
struct NodeKindInfo {
    id: u16,
    name: String,
    named: bool,
    visible: bool,
    supertype: bool,
}

/// Simple “extract grammar” helper that dumps node kinds as JSON.
fn extract_grammar(lang: &Language) -> serde_json::Value {
    let count = lang.node_kind_count();

    let mut kinds = Vec::with_capacity(count);
    for id in 0..count as u16 {
        if let Some(name) = lang.node_kind_for_id(id) {
            kinds.push(NodeKindInfo {
                id,
                name: name.to_string(),
                named: lang.node_kind_is_named(id),
                visible: lang.node_kind_is_visible(id),
                supertype: lang.node_kind_is_supertype(id),
            });
        }
    }

    serde_json::json!({
        "name": lang.name().unwrap_or("unknown"),
        "abi_version": lang.abi_version(),
        "node_kinds": kinds,
    })
}

fn main() -> anyhow::Result<()> {
    // 1. Load Lean.so (adjust the path to wherever it lives)
    let loaded = unsafe { load_lean_language("./Lean.so")? };
    let lang = &loaded.lang;

    // 2. Create a parser that uses this language
    let mut parser = Parser::new();
    parser.set_language(lang)?;

    // 3. Load a Lean source file
    let source = std::fs::read_to_string("example.lean")?;

    // 4. Parse it
    let tree = parser.parse(&source, None).expect("parse failed");
    let root = tree.root_node();
    println!("Root kind: {}", root.kind());

    // 5. Extract / print the grammar info
    let grammar = extract_grammar(lang);
    println!("{}", serde_json::to_string_pretty(&grammar)?);

    Ok(())
}
