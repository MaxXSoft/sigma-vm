/// ID of an entry.
pub type EntryId = u64;

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
}

/// Root entry.
///
/// A compile unit must have exactly one root entry.
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
  /// Implicit parameters.
  pub implicit_params: Vec<ImplicitParam>,
  /// Parameters.
  pub params: Vec<Param>,
  /// ID of return type.
  pub ret_ty: EntryId,
  /// Bounds.
  pub bounds: Vec<Bound>,
}

/// Implicit parameter.
#[derive(Debug)]
pub struct ImplicitParam {
  /// ID of parameter type.
  pub ty: EntryId,
  /// Optional.
  pub opt: bool,
}

/// Parameter.
#[derive(Debug)]
pub struct Param {
  /// ID of parameter type.
  pub ty: EntryId,
}

/// Bound.
#[derive(Debug)]
pub struct Bound {
  // TODO
}

/// Trait entry.
#[derive(Debug)]
pub struct Trait {
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
  // TODO
}
