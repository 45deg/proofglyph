From Stdlib Require Import List.
From Proofglyph.Language Require Import WeakChecker.
Import ListNotations.

Definition delta := tLam tType (tApp (tVar 0) (tVar 0)).
Definition omega := tApp delta delta.
Definition beta_identity := tApp (tLam tType (tVar 0)) (tConst 0).

(** Diverging children are irrelevant to exposing an outer binder or neutral. *)
Example whnf_preserves_lambda :
  whnf 20 (tLam tType omega) = Some (tLam tType omega).
Proof. reflexivity. Qed.
Example whnf_preserves_pi : whnf 20 (tPi tType omega) = Some (tPi tType omega).
Proof. reflexivity. Qed.
Example whnf_preserves_argument :
  whnf 20 (tApp (tConst 0) omega) = Some (tApp (tConst 0) omega).
Proof. reflexivity. Qed.
Example full_normal_exhausts : normal 20 (tLam tType omega) = None.
Proof. vm_compute; reflexivity. Qed.

(** Conversion still descends into binders and neutral arguments. *)
Example compare_pi_body : w_equal 20 (tPi tType beta_identity) (tPi tType (tConst 0)) = true.
Proof. vm_compute; reflexivity. Qed.
Example compare_lambda_body : w_equal 20 (tLam tType beta_identity) (tLam tType (tConst 0)) = true.
Proof. vm_compute; reflexivity. Qed.
Example compare_neutral_argument :
  w_equal 20 (tApp (tConst 1) beta_identity) (tApp (tConst 1) (tConst 0)) = true.
Proof. vm_compute; reflexivity. Qed.
Example compare_domain_mismatch :
  w_equal 20 (tPi tType (tConst 0)) (tPi tKind (tConst 0)) = false.
Proof. vm_compute; reflexivity. Qed.
Example compare_exhaustion : w_equal 1 beta_identity (tConst 0) = false.
Proof. vm_compute; reflexivity. Qed.
Example compare_identical_without_fuel : w_equal 0 omega omega = true.
Proof. vm_compute; reflexivity. Qed.
(** A : Type, x : A, P : A -> Type, f : A -> P ((fun y : A => y) x). *)
Definition indexed_redex :=
  tApp (tConst 2) (tApp (tLam (tConst 0) (tVar 0)) (tConst 1)).
Definition indexed_signature :=
  [tType; tConst 0; tPi (tConst 0) tType; tPi (tConst 0) indexed_redex].
Example indexed_signature_accepted :
  check_program 20 true [] (map Assume indexed_signature) = Some indexed_signature.
Proof. vm_compute; reflexivity. Qed.
Example infer_unreduced_codomain :
  infer 20 indexed_signature [] (tApp (tConst 3) (tConst 1)) = Some indexed_redex.
Proof. vm_compute; reflexivity. Qed.
Example full_infer_reduces_codomain :
  CheckerImpl.infer 20 indexed_signature [] (tApp (tConst 3) (tConst 1)) =
    Some (tApp (tConst 2) (tConst 1)).
Proof. vm_compute; reflexivity. Qed.
