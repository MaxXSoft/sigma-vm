# Syntax of Xeno

```ebnf
CompUnit := {[Anno] Item};
Anno := "@" IDENT {TOKEN};
Item := Import | Static | FuncDef | NativeDecl | Trait | Impl;

Import := "import" (Path | Paths);
Path := IDENT {"." IDENT} ["." (Paths | "*")];
Paths := "{" Path {"," Path} [","] "}";

Static := ["pub"] "static" ["mut"] IDENT ":" Type "=" Expr;

FuncDef := FuncDecl Block;
FuncDecl := ["pub"] "fn" IDENT [ImplicitParams] [Params] ["->" Type] [Where];

NativeDecl := "native" Path NativeBody;
NativeBody := "{" {FuncDecl} "}";

Trait := ["pub"] "trait" IDENT [ImplicitParams] [Params] [Inherit] [Where] TraitBody;
Inherit := ":" PathExpr {"+" PathExpr};
TraitBody := "{" {FuncDecl | FuncDef} "}";

Impl := "impl" [ImplicitParams] [PathExpr "for"] PathExpr [Where] ImplBody;
ImplBody := "{" {FuncDef} "}";

ImplicitParams := "[" [ImplicitParam {"," ImplicitParam} [","]] "]";
ImplicitParam := (["..."] IDENT | Param) ["=" Expr];
ImplicitArgs := "[" [Expr {"," Expr} [","]] "]";
Params := "(" [Param {"," Param} [","]] ")";
Param := ["..."] IDENT ":" Type;
Args := "(" [Expr {"," Expr} [","]] ")";

Where := "where" Bound {"," Bound} [","];
Bound := TraitBound | TypeBound;
TraitBound := PathExpr ":" PathExpr {"+" PathExpr};
TypeBound := PathExpr "=" PathExpr;

Type := PrimType | StructType | EnumType | ArrayType | TupleType
      | FuncType | TypeOfType | TraitType | SelfType;
PrimType := "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
          | "f32" | "f64" | "char" | "str" | "!";
StructType := "struct" "{" [StructField {"," StructField} [","]] "}";
StructField := ["pub"] IDENT ":" Type;
EnumType := "enum" "{" [EnumVariant {"," EnumVariant} [","]] "}";
EnumVariant := IDENT [TupleType] ["=" Expr];
ArrayType := "[" Type "]";
TupleType := "(" [Types] ")";
Types := ["..."] Type {"," ["..."] Type} [","];
FuncType := "fn" [ImplicitParamsType] [ParamsType] ["->" Type];
ImplicitParamsType := "[" [Types] "]";
ParamsType := "(" [Types] ")";
TypeOfType := "type" [TraitTypeBound | ValueTypeBound];
TraitTypeBound := "+" PathExpr [TraitTypeBound];
ValueTypeBound := ":" TraitType;
TraitType := PathExpr [TraitTypeBound];
SelfType := "Self";

Statement := Item | Let | Expr;
Let := "let" ["mut"] ConcretePat [":" Type] "=" Expr;

ConcretePat := VarPat | Underscore | TuplePat | ArrayPat | StructPat | EnumPat;
Pattern := ".." | ConcretePat;
VarPat := IDENT ["@" ConcretePat];
TuplePat := "(" [Pattern {"," Pattern} [","]] ")";
ArrayPat := "[" [Pattern {"," Pattern} [","]] "]";
StructPat := PathExpr "{" [FieldPat {"," FieldPat} [","]] "}";
FieldPat := IDENT [":" ConcretePat] | "..";
EnumPat := PathExpr [TuplePat];

Expr := BinaryExpr {Suffix};
Suffix := CallArgs | Access | Try;
CallArgs := ImplicitArgs [Args] | Args;
Access := "." PathExpr;
Try := "?";
BinaryExpr := Prefix {Op Prefix};
Prefix := {Op} Factor;
Op := PRE_DEF_OPS | IDENT;

Factor := Block | While | Break | Continue | If | Return | Literal
        | Underscore | ParenOrTupleExpr | ArrayExpr | Closure | Expand
        | TypeExpr | PathOrStructExpr;
Block := "{" [Statement {";" Statement} [";"]] "}";
While := [Label ":"] "while" Cond Block;
Label := "@" IDENT;
Cond := Expr | Let;
Break := "break" [Label];
Continue := "continue" [Label];
If := "if" Cond Block ["else" (If | Block)];
Return := "return" [Expr];

Literal := INT | FLOAT | CHAR | BYTE | STR | RAW_STR | BYTES;
Underscore := "_";
ParenOrTupleExpr := "(" [Expr {"," Expr} [","]] ")";
ArrayExpr := "[" [Expr {"," Expr} [","]] "]";
Closure := "fn" [ImplicitClosureParams] [ClosureParams] ["->" Type] [Where] Expr;
ImplicitClosureParams := "[" [ClosureParam {"," ClosureParam} [","]] "]";
ClosureParams := "(" [ClosureParam {"," ClosureParam} [","]] ")";
ClosureParam := IDENT [":" Type];
Expand := "..." Expr;
TypeExpr := "type" Type;
PathOrStructExpr := PathExpr [StructExpr];
PathExpr := IDENT [ImplicitArgs] [Args] ["." PathExpr];
StructExpr := "{" [FieldExpr {"," FieldExpr} [","]] "}";
FieldExpr := IDENT [":" Expr] | ".." Expr;
```
