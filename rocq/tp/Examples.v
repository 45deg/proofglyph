From Stdlib Require Import List String.
From Tinyprover.Pa Require Import Syntax Program.
From Tinyprover.Tp Require Import Surface Resolve Compile.
Import ListNotations.
Open Scope string_scope.

Example anonymous_binder_counts :
  resolve ["A"; "B"] [Some "x"] (Product None (Name "A") (Apply (Name "B") (Name "x"))) =
    Some (tPi (tConst 0) (tApp (tConst 1) (tVar 1))).
Proof. reflexivity. Qed.

Example local_shadows_global : resolve ["x"] [None; Some "x"; Some "x"] (Name "x") = Some (tVar 1).
Proof. reflexivity. Qed.

Example annotation_uses_outer_scope :
  resolve ["A"] [] (Lambda "A" (Name "A") (Name "A")) =
    Some (tLam (tConst 0) (tVar 0)).
Proof. reflexivity. Qed.

Definition identity_source := [Decl "A" Universe None;
  Decl "id" (Product (Some "x") (Name "A") (Name "A"))
    (Some (Lambda "x" (Name "A") (Name "x")))].

Example checked_identity : compile 32 true identity_source = Some
  ([Assume tType; Prove (tPi (tConst 0) (tConst 0)) (tLam (tConst 0) (tVar 0))],
   [tType; tPi (tConst 0) (tConst 0)]).
Proof. reflexivity. Qed.

Example duplicate_rejected : lower [] [Decl "A" Universe None; Decl "A" Universe None] = None.
Proof. reflexivity. Qed.

Example forward_rejected : lower [] [Decl "a" (Name "A") None; Decl "A" Universe None] = None.
Proof. reflexivity. Qed.

Example self_rejected : lower [] [Decl "A" (Name "A") None] = None.
Proof. reflexivity. Qed.

Example ill_typed_rejected : compile 32 true [Decl "bad" Top None] = None.
Proof. reflexivity. Qed.

Example axioms_forbidden : compile 32 false identity_source = None.
Proof. reflexivity. Qed.
