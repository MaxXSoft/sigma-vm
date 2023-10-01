# Syntax of Xeno

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
EnumType := "enum" "{" [EnumField {"," EnumField} [","]] "}";
EnumField := IDENT [TupleType] ["=" Expr];
ArrayType := "[" Type ";" Expr "]";
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

ConcretePat := VarPat | TuplePat | ArrayPat | StructPat | EnumPat;
Pattern := ".." | ConcretePat;
VarPat := IDENT ["@" ConcretePat] | Underscore;
TuplePat := "(" [Pattern {"," Pattern} [","]] ")";
ArrayPat := "[" [Pattern {"," Pattern} [","]] "]";
StructPat := PathExpr "{" [FieldPat {"," FieldPat} [","]] "}";
FieldPat := IDENT [":" ConcretePat] | "..";
EnumPat := PathExpr [TuplePat];

Expr := Prefix {PathExpr Prefix};
Prefix := {PathExpr} Factor;
Factor := Block | NonBlock;
Block := "{" {Statement} "}";
NonBlock := Loop | While | Break | Continue | If | Match | Return
          | Literal | Underscore | Bang | Paren | TupleExpr | ArrayExpr
          | StructExpr | Call | PathExpr | Access | Closure | Expand
          | Type;
Loop := [Label ":"] "loop" Block;
While := [Label ":"] "while" Cond Block;
Label := "@" IDENT;
Cond := Expr | Let;
Break := "break" [Label];
Continue := "continue" [Label];
If := "if" Cond Block ["else" (If | Block)];
Match := "match" Expr "{" MatchArm {MatchArm} "}";
MatchArm := ConcretePat "=>" (Block [","] | NonBlock ",");
Return := "return" [Expr];

Literal := INT | FLOAT | CHAR | BYTE | STR | RAW_STR | BYTES;
Underscore := "_";
Bang := "!";
Paren := "(" Expr ")";
TupleExpr := "(" [Expr "," {Expr ","} [Expr]] ")";
ArrayExpr := "[" [Expr {"," Expr} [","]] "]";
StructExpr := PathExpr "{" [FieldExpr {"," FieldExpr} [","]] "}";
FieldExpr := IDENT [":" Expr] | ".." Expr;
Call := Expr CallArgs;
CallArgs := ImplicitArgs | Args | ImplicitArgs Args;
PathExpr := IDENT [ImplicitArgs] [Args] ["." PathExpr];
Access := Expr "." PathExpr;
Closure := "fn" [ImplicitClosureParams] [ClosureParams] ["->" Type] [Where] Expr;
ImplicitClosureParams := "[" [ClosureParam {"," ClosureParam} [","]] "]";
ClosureParams := "(" [ClosureParam {"," ClosureParam} [","]] ")";
ClosureParam := IDENT [":" Type];
Expand := "..." [PathExpr] Paren;
```