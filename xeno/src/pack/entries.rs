use std::num::NonZeroU64;

/// ID of an entry.
///
/// The ID zero is always preserved for the root entry.
pub type EntryId = NonZeroU64;

/// Entry.
#[derive(Debug)]
pub enum Entry {
  /// Root entry.
  Root(Root),
  /// Package.
  Pack(Pack),
  /// Static variable.
  Static(Static),
  /// Function (including native function declarations).
  Func(Func),
  /// Trait.
  Trait(Trait),
  /// Implementation.
  Impl(Impl),
  /// Type.
  Type(Type),
  /// Reference of entry in another compile unit.
  Ref(Ref),
  /// HIR, for representing function definitions and values.
  Hir(Hir),
}

/// Root entry.
///
/// A compile unit must have exactly one root entry.
/// The ID of the root entry must be zero.
#[derive(Debug)]
pub struct Root {
  /// The package path of the current compile unit (dot-delimited).
  pub path: String,
  /// All sub-entries.
  pub entries: Vec<EntryId>,
}

/// Package entry.
#[derive(Debug)]
pub struct Pack {
  /// Name of the package.
  pub name: String,
  /// All sub-entries.
  pub entries: Vec<EntryId>,
}

/// Static variable entry.
#[derive(Debug)]
pub struct Static {
  /// Name of the static variable.
  pub name: String,
  /// ID of the static variable type.
  pub ty: EntryId,
}

/// Function entry.
#[derive(Debug)]
pub struct Func {
  /// Name of the function.
  pub name: String,
  /// Kind of the function.
  pub kind: FuncKind,
}

/// Kind of function.
#[derive(Debug)]
pub enum FuncKind {
  /// Specialized function.
  Specialized(FuncData),
  /// Generic function, with an ID of HIR entry.
  Generic(EntryId),
}

/// Data of function.
#[derive(Debug)]
pub struct FuncData {
  /// Implicit parameters.
  pub implicit_params: Vec<ImplicitParam>,
  /// Parameters.
  pub params: Vec<Param>,
  /// ID of return type.
  pub ret_ty: EntryId,
}

/// Implicit parameter.
#[derive(Debug)]
pub struct ImplicitParam {
  /// ID of parameter type.
  pub ty: EntryId,
  /// Default value.
  pub default: Option<EntryId>,
}

/// Parameter.
#[derive(Debug)]
pub struct Param {
  /// ID of parameter type.
  pub ty: EntryId,
}

/// Trait entry.
#[derive(Debug)]
pub struct Trait {
  /// Name of the trait.
  pub name: String,
  // TODO
}

/// Implementation entry.
#[derive(Debug)]
pub struct Impl {
  // TODO
}

/// Type entry.
#[derive(Debug)]
pub struct Type {
  // TODO
}

/// Reference entry.
#[derive(Debug)]
pub struct Ref {
  /// Path of the referenced entry (dot-delimited).
  pub path: String,
  /// ID of the referenced entry.
  pub id: EntryId,
}

/// HIR entry.
#[derive(Debug)]
pub struct Hir {
  // TODO
}
