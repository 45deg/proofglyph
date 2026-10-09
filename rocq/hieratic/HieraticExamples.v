From Stdlib Require Import List String.
From Tinyprover.Hieratic Require Import Desugar HieraticSyntax HieraticImports.
Import ListNotations.
Open Scope string_scope.

Example lexer_comments : lex_hieratic "// ignored
axiom A' : Type;" = Some [Word "axiom"; Word "A'"; Word ":"; Word "Type"; Word ";"].
Proof. reflexivity. Qed.
Example precedence : parse_hieratic "axiom f : A B -> C -> D;" = Some
  [HieraticDeclaration (RawDecl "f" (RForall PNil
    (RArrow (RApply (RName "A") (RName "B")) (RArrow (RName "C") (RName "D")))) None)].
Proof. reflexivity. Qed.
Example grouped_declaration : parse_hieratic "def f (x y : A) : A := x;" = Some
  [HieraticDeclaration (RawDecl "f" (RForall (PGroup "x" ["y"] (RName "A") PNil) (RName "A"))
    (Some (RLambda (PGroup "x" ["y"] (RName "A") PNil) (RName "x"))))].
Proof. reflexivity. Qed.
Example reject_reserved : parse_hieratic "axiom import : Type;" = None.
Proof. reflexivity. Qed.
Example reject_empty_group : parse_hieratic "axiom f () : Type;" = None.
Proof. reflexivity. Qed.
Example reject_empty_import : parse_hieratic "import """";" = None.
Proof. reflexivity. Qed.
Definition base := RawDecl "A" (RForall PNil RType) None.
Definition left := RawDecl "left" (RForall PNil (RName "A")) None.
Definition right := RawDecl "right" (RForall PNil (RName "A")) None.
Example diamond : load_hieratic
  [("entry",[HieraticImport "left";HieraticImport "right"]);
   ("left",[HieraticImport "base";HieraticDeclaration left]);
   ("right",[HieraticImport "base";HieraticDeclaration right]);
   ("base",[HieraticDeclaration base])] "entry" = Some [base;left;right].
Proof. reflexivity. Qed.
Example cycle : load_hieratic [("a",[HieraticImport "b"]);("b",[HieraticImport "a"])] "a" = None.
Proof. reflexivity. Qed.
Example missing : load_hieratic [("a",[HieraticImport "missing"])] "a" = None.
Proof. reflexivity. Qed.
Example declaration_position : load_hieratic
  [("a",[HieraticDeclaration left;HieraticImport "base";HieraticDeclaration right]);
   ("base",[HieraticDeclaration base])] "a" = Some [left;base;right].
Proof. reflexivity. Qed.
