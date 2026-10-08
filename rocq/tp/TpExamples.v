From Stdlib Require Import List String.
From Tinyprover.Tp Require Import Desugar TpSyntax TpImports.
Import ListNotations.
Open Scope string_scope.

Example lexer_comments : lex_tp "// ignored
axiom A' : Type;" = Some [Word "axiom"; Word "A'"; Word ":"; Word "Type"; Word ";"].
Proof. reflexivity. Qed.
Example precedence : parse_tp "axiom f : A B -> C -> D;" = Some
  [TpDeclaration (RawDecl "f" (RForall PNil
    (RArrow (RApply (RName "A") (RName "B")) (RArrow (RName "C") (RName "D")))) None)].
Proof. reflexivity. Qed.
Example grouped_declaration : parse_tp "def f (x y : A) : A := x;" = Some
  [TpDeclaration (RawDecl "f" (RForall (PGroup "x" ["y"] (RName "A") PNil) (RName "A"))
    (Some (RLambda (PGroup "x" ["y"] (RName "A") PNil) (RName "x"))))].
Proof. reflexivity. Qed.
Example reject_reserved : parse_tp "axiom import : Type;" = None.
Proof. reflexivity. Qed.
Example reject_empty_group : parse_tp "axiom f () : Type;" = None.
Proof. reflexivity. Qed.
Example reject_empty_import : parse_tp "import """";" = None.
Proof. reflexivity. Qed.
Definition base := RawDecl "A" (RForall PNil RType) None.
Definition left := RawDecl "left" (RForall PNil (RName "A")) None.
Definition right := RawDecl "right" (RForall PNil (RName "A")) None.
Example diamond : load_tp
  [("entry",[TpImport "left";TpImport "right"]);
   ("left",[TpImport "base";TpDeclaration left]);
   ("right",[TpImport "base";TpDeclaration right]);
   ("base",[TpDeclaration base])] "entry" = Some [base;left;right].
Proof. reflexivity. Qed.
Example cycle : load_tp [("a",[TpImport "b"]);("b",[TpImport "a"])] "a" = None.
Proof. reflexivity. Qed.
Example missing : load_tp [("a",[TpImport "missing"])] "a" = None.
Proof. reflexivity. Qed.
Example declaration_position : load_tp
  [("a",[TpDeclaration left;TpImport "base";TpDeclaration right]);
   ("base",[TpDeclaration base])] "a" = Some [left;base;right].
Proof. reflexivity. Qed.
