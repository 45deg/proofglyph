From Stdlib Require Import List String.
From Proofglyph.Language Require Import Syntax.
From Proofglyph.Hieratic Require Import Surface Desugar Resolve SurfaceCompile.
Import ListNotations.
Open Scope string_scope.

Example grouped_names_are_sequential :
  desugar (RLambda (PGroup "x" ["y"] (RName "A") PNil) (RName "x")) =
  Lambda "x" (Name "A") (Lambda "y" (Name "A") (Name "x")).
Proof. reflexivity. Qed.

Example annotation_shadowing_is_sequential :
  resolve ["A"; "B"] [Some "x"]
    (desugar (RLambda (PGroup "x" ["y"] (RApply (RName "B") (RName "x")) PNil)
      (RName "y"))) =
  Some (tLam (tApp (tConst 1) (tVar 0))
    (tLam (tApp (tConst 1) (tVar 0)) (tVar 0))).
Proof. reflexivity. Qed.

Example arrow_preserves_anonymous_depth :
  resolve ["A"; "B"] [Some "x"]
    (desugar (RArrow (RName "A") (RApply (RName "B") (RName "x")))) =
  Some (tPi (tConst 0) (tApp (tConst 1) (tVar 1))).
Proof. reflexivity. Qed.

Example nested_sugar_in_annotation :
  desugar (RForall (PGroup "f" [] (RArrow (RName "A") (RName "A")) PNil)
    (RApply (RName "f") (RName "a"))) =
  Product (Some "f") (Product None (Name "A") (Name "A")) (Apply (Name "f") (Name "a")).
Proof. reflexivity. Qed.

Example no_parameters_is_identity :
  desugar (RForall PNil RType) = Universe /\ desugar (RLambda PNil RType) = Universe.
Proof. split; reflexivity. Qed.

Example grouped_source_to_proofglyph : compile_surface_proofglyph 32 true
  [RawDecl "A" RType None false;
   RawDecl "keep"
     (RForall (PGroup "x" ["y"] (RName "A") PNil) (RName "A"))
     (Some (RLambda (PGroup "x" ["y"] (RName "A") PNil) (RName "x"))) true] =
  Some ("*:#0#0#0>>#0#0$1\\!", [tType; tPi (tConst 0) (tPi (tConst 0) (tConst 0))]).
Proof. reflexivity. Qed.
