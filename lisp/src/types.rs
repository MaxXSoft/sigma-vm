/// Type of value.
#[derive(Debug, Clone)]
enum Type {
  /// Number.
  Num,
  /// String.
  Str,
  /// Symbol.
  Sym,
  /// List.
  List(Vec<Type>),
  /// Lambda, with parameter types and return type.
  Lambda(Vec<Type>, Box<Type>),
  /// Unknown.
  Unknown,
}
