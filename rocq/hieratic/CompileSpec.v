From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Tinyprover.Proofglyph Require Export Syntax Program WellFormed.
From Tinyprover.Hieratic Require Export ResolveSpec.

Inductive translates_decl (gs : globals) : source_decl -> declaration -> Prop :=
| translates_assume : forall n a a',
    resolves gs [] a a' -> translates_decl gs (Decl n a None) (Assume a')
| translates_prove : forall n a b a' b',
    resolves gs [] a a' -> resolves gs [] b b' ->
    translates_decl gs (Decl n a (Some b)) (Prove a' b').

(** Source order, declaration kinds and the preceding-name environment are
    part of the specification, rather than inferred from checker acceptance. *)
Inductive translates : globals -> list source_decl -> list declaration -> Prop :=
| translates_nil : forall gs, translates gs [] []
| translates_cons : forall gs d rest d' rest',
    ~ In (decl_name d) gs -> translates_decl gs d d' ->
    translates (gs ++ [decl_name d]) rest rest' ->
    translates gs (d :: rest) (d' :: rest').

Definition core_is_assumption d := match d with Assume _ => true | Prove _ _ => false end.

Theorem translates_kinds gs src ds :
  translates gs src ds -> map is_assumption src = map core_is_assumption ds.
Proof.
  intros H; induction H; cbn; [reflexivity|].
  rewrite IHtranslates; destruct H0; reflexivity.
Qed.

Theorem translates_length gs src ds : translates gs src ds -> List.length src = List.length ds.
Proof. intros H; induction H; cbn; congruence. Qed.

Lemma translates_fresh gs src ds : translates gs src ds ->
  forall n, In n gs -> ~ In n (map decl_name src).
Proof.
  intros H; induction H; intros n IN; cbn; [tauto|].
  intros [E|TAIL].
  - subst; contradiction.
  - apply (IHtranslates n); [apply in_or_app; left; exact IN|exact TAIL].
Qed.

Theorem translates_distinct gs src ds : translates gs src ds -> NoDup (map decl_name src).
Proof.
  intros H; induction H; cbn; constructor; [|assumption].
  eapply translates_fresh; [exact H1|].
  apply in_or_app; right; cbn; auto.
Qed.

Definition source_permitted allow src :=
  Forall (fun d => match decl_body d with None => allow = true | Some _ => True end) src.

Theorem translates_policy allow gs src ds : translates gs src ds ->
  (source_permitted allow src <-> permitted_declarations allow ds).
Proof.
  intros H; induction H; unfold source_permitted, permitted_declarations in *.
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, <- IHtranslates; destruct H0; reflexivity.
Qed.

Fixpoint scoped_declarations (n : nat) (ds : list declaration) : Prop :=
  match ds with
  | [] => True
  | d :: rest => scoped n 0 (declared_type d) /\
      (match d with Assume _ => True | Prove _ b => scoped n 0 b end) /\
      scoped_declarations (S n) rest
  end.

Theorem translates_scoped gs src ds :
  translates gs src ds -> scoped_declarations (List.length gs) ds.
Proof.
  intros H; induction H; cbn; [exact I|].
  rewrite length_app in IHtranslates; cbn in IHtranslates.
  rewrite Nat.add_1_r in IHtranslates.
  destruct H0; cbn; repeat split; auto;
    eapply resolves_scoped with (ls := []); eauto.
Qed.


Lemma translates_decl_unique gs d a b : translates_decl gs d a -> translates_decl gs d b -> a = b.
Proof. intros A B; inversion A; subst; inversion B; subst; f_equal; eauto using resolves_unique. Qed.
Theorem translates_unique gs src ds es : translates gs src ds -> translates gs src es -> ds = es.
Proof.
  intros A; revert es; induction A; intros es B; inversion B; subst;
    f_equal; eauto using translates_decl_unique.
Qed.
