# Syntax of Xeno

```ebnf
CompUnit := {[Anno] ItemWithSemicolon};
Anno := "@" Ident {TOKEN};
ItemWithSemicolon := Item {";"};
Item := Pack | Import | Static | FuncDef | NativeDecl | Trait | Impl;

Pack := ["pub"] "pack" Ident "{" {ItemWithSemicolon} "}";

Import := "import" (ImportPath | ImportPaths);
ImportPath := Path ["." (ImportPaths | "*")];
Path := Ident {"." Ident};
ImportPaths := "{" ImportPath {"," ImportPath} [","] "}";

Static := ["pub"] "static" ["mut"] Ident ":" Type "=" Expr;

FuncDef := FuncDecl Block;
FuncDecl := ["pub"] "fn" Ident [ImplicitParams] [Params] ["->" Type] [Where];

NativeDecl := "native" Path NativeBody;
NativeBody := "{" {FuncDecl} "}";

Trait := ["pub"] "trait" Ident [ImplicitParams] [Params] [Inherit] [Where] TraitBody;
Inherit := ":" PathExpr {"+" PathExpr};
TraitBody := "{" {FuncDecl | FuncDef} "}";

Impl := "impl" [ImplicitParams] [PathExpr "for"] PathExpr [Where] ImplBody;
ImplBody := "{" {FuncDef} "}";

ImplicitParams := "[" [ImplicitParam {"," ImplicitParam} [","]] "]";
ImplicitParam := (["..."] Ident | Param) ["=" Expr];
ImplicitArgs := "[" [Expr {"," Expr} [","]] "]";
Params := "(" [Param {"," Param} [","]] ")";
Param := ["..."] Ident ":" Type;
Args := "(" [Expr {"," Expr} [","]] ")";

Where := "where" Bound {"," Bound} [","];
Bound := ["..."] (TraitBound | TypeBound);
TraitBound := PathExpr ":" PathExpr {"+" PathExpr};
TypeBound := PathExpr "=" Expr;

Type := PrimType | StructType | EnumType | ArrayType | TupleType
      | FuncType | TypeOfType | TraitType | SelfType;
PrimType := "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64"
          | "f32" | "f64" | "char" | "str" | "!";
StructType := "struct" "{" [StructField {"," StructField} [","]] "}";
StructField := ["pub"] Ident ":" Type;
EnumType := "enum" "{" [EnumVariant {"," EnumVariant} [","]] "}";
EnumVariant := Ident [TupleType | "=" Expr];
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
VarPat := Ident ["@" ConcretePat];
TuplePat := "(" [Pattern {"," Pattern} [","]] ")";
ArrayPat := "[" [Pattern {"," Pattern} [","]] "]";
StructPat := PathExpr "{" [FieldPat {"," FieldPat} [","]] "}";
FieldPat := Ident [":" ConcretePat] | "..";
EnumPat := PathExpr [TuplePat];

Expr := Prefix {Ident Prefix};
Prefix := {Op} Factor {Suffix};
Suffix := CallArgs | Access | Try | Cast;
CallArgs := ImplicitArgs [Args] | Args;
Access := "." PathExpr;
Try := "?";
Cast := "as" (Underscore | Type);
Ident := Op | IDENT;
Op := PRE_DEF_OPS | OP_LIKE;

Factor := Block | While | Break | Continue | If | Return | Literal
        | Underscore | ParenOrTupleExpr | ArrayExpr | Closure | Expand
        | TypeExpr | PathOrStructExpr;
Block := "{" {BlockStatement} "}";
BlockStatement := Statement [";"] | ";";
While := [Label ":"] "while" Cond Block;
Label := "@" Ident;
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
ClosureParam := Ident [":" Type];
Expand := "..." Expr;
TypeExpr := "type" Type;
PathOrStructExpr := PathExpr [StructExpr];
PathExpr := Ident [ImplicitArgs] [Args] ["." PathExpr];
StructExpr := "{" [FieldExpr {"," FieldExpr} [","]] "}";
FieldExpr := Ident [":" Expr] | ".." Expr;
```
