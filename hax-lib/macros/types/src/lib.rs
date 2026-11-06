use serde::{Deserialize, Serialize};

/// Each item can be marked with a *u*nique *id*entifier. This is
/// useful whenever the payload of an attribute is a piece of Rust code
/// (an expression, a path, a type...). We don't want to retrieve those
/// pieces of Rust code as raw token stream: we want to let Rustc give
/// meaning to those. For instance, we want Rustc to type expressions
/// and to resolve paths.
///
/// Thus, we expand attributes with Rust-code-payloads as top-level
/// items marked with an `ItemUid`. The attributes are then replaced
/// in place with a simple reference (the `ItemUid` in stake).
///
/// Morally, we expand `struct Foo { #[refine(x > 3)] x: u32 }` to:
///  1. `#[uuid(A_UNIQUE_ID_123)] fn refinement(x: u32) -> hax_lib::Prop {x > 3}`;
///  2. `struct Foo { #[refined_by(A_UNIQUE_ID_123)] x: u32 }`.
#[derive(Debug, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaUid")]
pub struct ItemUid {
    /// Currently, this is a UUID.
    pub uid: String,
}

impl std::fmt::Display for ItemUid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.uid, f)
    }
}

impl ItemUid {
    pub fn fresh() -> Self {
        use uuid::Uuid;
        let uid = format!("{}", Uuid::new_v4().simple());
        ItemUid { uid }
    }
}

/// What shall Hax do with an item?
#[derive(Debug, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaItemStatus")]
pub enum ItemStatus {
    /// Include this item in the translation
    Included {
        /// Should Hax drop this item just before code generation?
        late_skip: bool,
    },
    /// Exclude this item from the translation, optionally replacing it in the backends
    Excluded { modeled_by: Option<String> },
}

/// An item can be associated to another one for multiple reasons:
/// `AssociationRole` capture the nature of the (directed) relation
/// between two items
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaAssocRole")]
pub enum AssociationRole {
    Requires,
    Ensures,
    Decreases,
    SMTPat,
    Refine,
    /// A quoted piece of backend code to place after or before the
    /// extraction of the marked item
    ItemQuote,
    ProcessRead,
    ProcessWrite,
    ProcessInit,
    ProtocolMessages,
}

/// Where should a item quote appear?
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaItemQuotePosition")]
pub enum ItemQuotePosition {
    /// Should appear just before the item in the extraction
    Before,
    /// Should appear right after the item in the extraction
    After,
}

/// F*-specific options for item quotes
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaItemQuoteFStarOpts")]
pub struct ItemQuoteFStarOpts {
    /// Shall we output this in F* interfaces (`*.fsti` files)?
    pub intf: bool,
    /// Shall we output this in F* implementations (`*.fst` files)?
    pub r#impl: bool,
}

/// An item quote is a verbatim piece of backend code included in
/// Rust. [`ItemQuote`] encodes the various options a item quote can
/// have.
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaItemQuote")]
pub struct ItemQuote {
    pub position: ItemQuotePosition,
    pub fstar_options: Option<ItemQuoteFStarOpts>,
}

/// The proof method to use for verification condition generation and discharge.
#[derive(Debug, Copy, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaProofMethod")]
pub enum ProofMethod {
    BvDecide,
    Grind,
}

/// Hax only understands one attribute: `#[hax::json(PAYLOAD)]` where
/// `PAYLOAD` is a JSON serialization of an inhabitant of
/// `AttrPayload`.
#[derive(Debug, Clone, Serialize, Deserialize, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "schemars", derive(schemars::JsonSchema))]
#[serde(rename = "HaPayload")]
pub enum AttrPayload {
    ItemStatus(ItemStatus),
    /// Mark an item as associated with another one
    AssociatedItem {
        /// What is the nature of the association?
        role: AssociationRole,
        /// What is the identifier of the target item?
        item: ItemUid,
    },
    Uid(ItemUid),
    /// Decides of the position of a item quote
    ItemQuote(ItemQuote),
    /// Mark an item so that hax never drop its body (this is useful
    /// for pre- and post- conditions of a function we dropped the
    /// body of: pre and post are part of type signature)
    NeverErased,
    NewtypeAsRefinement,
    /// Mark an item as a lemma statement to prove in the backend
    Lemma,
    Language,
    ProcessRead,
    ProcessWrite,
    ProcessInit,
    Proof(String),
    PureRequiresProof(String),
    PureEnsuresProof(String),
    ProofMethod(ProofMethod),
    ProtocolMessages,
    PVConstructor,
    PVHandwritten,
    PVInline,
    /// Exempt a function from the ProVerif backend's checks of its uses of
    /// `Result`
    PVUncheckedResults,
    TraitMethodNoPrePost,
    /// Make an item opaque
    Erased,
    /// In the context of a set of fields (e.g. on a `struct`), overrides its
    /// order. By default, the order of a field is its index, e.g. the first
    /// field has order 0, the i-th field has order i+1. Rust fields order
    /// matters: it rules how bits are represented. Once extracted, the order
    /// matters, but for different reasons, e.g. a field is refined with
    /// another, requiring a specific order.
    Order(i32),
}

pub const HAX_TOOL: &str = "_hax";
pub const HAX_CFG_OPTION_NAME: &str = "hax_compilation";

pub struct HaxTool;
pub struct HaxCfgOptionName;
pub struct DebugOrHaxCfgExpr;
impl ToTokens for HaxTool {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        format_ident!("{}", HAX_TOOL).to_tokens(tokens)
    }
}
impl ToTokens for HaxCfgOptionName {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        format_ident!("{}", HAX_CFG_OPTION_NAME).to_tokens(tokens)
    }
}
impl ToTokens for DebugOrHaxCfgExpr {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        quote! {any(#HaxCfgOptionName, debug_assertions)}.to_tokens(tokens)
    }
}

use quote::*;

impl From<&AttrPayload> for proc_macro2::TokenStream {
    fn from(payload: &AttrPayload) -> Self {
        let payload: String = serde_json::to_string(payload).unwrap();
        quote! {#[cfg_attr(#HaxCfgOptionName, #HaxTool::json(#payload))]}
    }
}

impl ToTokens for AttrPayload {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        proc_macro2::TokenStream::from(self).to_tokens(tokens)
    }
}
