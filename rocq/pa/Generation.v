From Stdlib Require Import List.
From Tinyprover.Pa Require Import Syntax Substitution WellFormed Confluence.
Import ListNotations.

Definition generates sg ctx t typ :=
  match t with
  | tType => conv tKind typ
  | tKind => False
  | tVar n => exists a, nth_error ctx n = Some a /\ conv (shift (S n) 0 a) typ
  | tConst n => exists a, nth_error sg n = Some a /\ conv a typ
  | tPi a b => exists s, typing sg ctx a tType /\ typing sg (a :: ctx) b s /\
      is_sort s /\ conv s typ
  | tLam a b => exists bt s, typing sg ctx a tType /\ typing sg (a :: ctx) b bt /\
      typing sg ctx (tPi a bt) s /\ is_sort s /\ conv (tPi a bt) typ
  | tApp f x => exists a b, typing sg ctx f (tPi a b) /\ typing sg ctx x a /\
      conv (instantiate b x) typ
  end.

Lemma generates_conv sg ctx t a b : generates sg ctx t a -> conv a b -> generates sg ctx t b.
Proof.
  destruct t; cbn [generates]; intros H C;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    eauto 10 using cv_trans; contradiction.
Qed.

Theorem typing_generation sg ctx t a : typing sg ctx t a -> generates sg ctx t a.
Proof.
  intros H; induction H; cbn [generates]; eauto 10 using cv_refl, generates_conv.
Qed.

Theorem typing_unique sg ctx t a b : typing sg ctx t a -> typing sg ctx t b -> conv a b.
Proof.
  revert ctx a b; induction t; intros ctx A B TA TB;
    apply typing_generation in TA; apply typing_generation in TB; cbn [generates] in *;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  - eapply cv_trans; [apply cv_sym; exact TA|exact TB].
  - contradiction.
  - match goal with H : nth_error _ _ = Some ?a, H' : nth_error _ _ = Some ?b |- _ =>
      rewrite H in H'; inversion H'; subst end.
    eauto using cv_trans, cv_sym.
  - match goal with H : nth_error _ _ = Some ?a, H' : nth_error _ _ = Some ?b |- _ =>
      rewrite H in H'; inversion H'; subst end.
    eauto using cv_trans, cv_sym.
  - eapply cv_trans; [apply cv_sym; eassumption|].
    eapply cv_trans; [eapply IHt2; eauto|eassumption].
  - eapply cv_trans; [apply cv_sym; eassumption|].
    eapply cv_trans; [apply cv_pi; [apply cv_refl|eapply IHt2; eauto]|eassumption].
  - match goal with F : typing sg ctx t1 (tPi ?a ?b), F' : typing sg ctx t1 (tPi ?c ?d) |- _ =>
      pose proof (conv_pi_injective _ _ _ _ (IHt1 _ _ _ F F')) as [_ BC] end.
    eapply cv_trans; [apply cv_sym; eassumption|].
    eapply cv_trans; [|eassumption].
    rewrite !instantiate_as_substitute; apply conv_substitute; exact BC.
Qed.
