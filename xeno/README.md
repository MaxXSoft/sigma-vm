# Xeno Programming Language

Xeno is a novel programming language designed to:

* Functional programming, generic typing, flexible macro system and so on.
* Supported both garbage collector and manual memory management.
* Coroutines and auto-parallelisation.
* High performance powered by Sigma VM.

## Syntax

```ebnf
CompUnit := {[Anno] Item};
Anno := "@" IDENT {TOKEN};
Item := Import | Static | FuncDef | NativeFuncDecl | Trait | Impl;

Import := "import" (Path | Paths);
Path := IDENT {"." IDENT} ["." (Paths | "*")];
Paths := "{" Path {"," Path} [","] "}";

Static := ["pub"] "static" ["mut"] IDENT ":" Type "=" Expr;

FuncDef := ["pub"] FuncDecl Block;
FuncDecl := "fn" IDENT [ImplicitParams] [Params] ["->" Type] [Where];

NativeFuncDecl := ["pub"] "native" FuncDecl;

Trait := ["pub"] "trait" IDENT [ImplicitParams] [Params] [Inherit] [Where] TraitBody;
Inherit := ":" PathExpr {"+" PathExpr};
TraitBody := "{" {FuncDecl [FuncBody]} "}";

Impl := "impl" [ImplicitParams] [PathExpr "for"] PathExpr [Where] ImplBody;
ImplBody := "{" {FuncDef} "}";

ImplicitParams := "[" [ImplicitParam {"," ImplicitParam} [","]] "]";
ImplicitParam := IDENT | Param;
ImplicitArgs := "[" [Expr {"," Expr} [","]] "]";
Params := "(" [Param {"," Param} [","]] ")";
Param := IDENT ":" Type;
Args := "(" [Expr {"," Expr} [","]] ")";

Where := "where" Bound {"," Bound} [","];
Bound := TraitBound | TypeBound;
TraitBound := PathExpr ":" PathExpr {"+" PathExpr};
TypeBound := PathExpr "=" PathExpr;

Type := PrimType | StructType | EnumType | ArrayType
      | TupleType | FuncType | TypeOfType | TraitType;
PrimType := "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
          | "f32" | "f64" | "bool" | "char" | "str" | "!";
StructType := "struct" "{" [StructField {"," StructField} [","]] "}";
StructField := ["pub"] IDENT ":" Type;
EnumType := "enum" "{" [EnumField {"," EnumField} [","]] "}";
EnumField := IDENT [TupleType] ["=" Expr];
ArrayType := "[" Type ";" Expr "]";
TupleType := "(" [Type {"," Type} [","]] ")";
FuncType := ...;
TypeOfType := "type" [TraitTypeBound | ValueTypeBound];
TraitTypeBound := "+" PathExpr [TraitTypeBound];
ValueTypeBound := ":" TraitType;
TraitType := PathExpr [TraitTypeBound];

Statement := Item | Let | Expr;
Let := "let" ["mut"] ConcretePat [":" Type] "=" Expr;

ConcretePat := VarPat | TuplePat | StructPat | EnumPat;
Pattern := ".." | ConcretePat;
VarPat := IDENT | Underscore;
TuplePat := "(" [Pattern {"," Pattern} [","]] ")";
StructPat := PathExpr "{" [FieldPat {"," FieldPat} [","]] "}";
FieldPat := IDENT [":" ConcretePat] | "..";
EnumPat := PathExpr [TuplePat];

Expr := Prefix {PathExpr Prefix};
Prefix := {PathExpr} Factor;
Factor := Block | Loop | While | If | Match | Return
        | Literal | Underscore | Paren | TupleExpr | Call
        | StructExpr | PathExpr | Closure;
Block := "{" {Statement} "}";
Loop := ...;
While := ...;
If := ...;
Match := ...;
Return := ...;
Literal := ...;
Underscore := "_";
Paren := "(" Expr ")";
TupleExpr := "(" [Expr "," {Expr ","} [Expr]] ")";
Call := Expr CallArgs;
CallArgs := ImplicitArgs | Args | ImplicitArgs Args;
StructExpr := ...;
PathExpr := IDENT [ImplicitArgs] [Args] ["." PathExpr];
Closure := ...;
```

TODO: Variadic parameters and expand syntax.
