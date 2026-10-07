From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Kernel WellFormed Completeness Confluence
  Regularity Arity Normalization Reducibility.

(** No termination or algorithmic-typing premise: this is strong normalization
    for the declarative lambda-Pi judgment under its well-formedness conditions. *)
Theorem typing_strong_normalization sg ctx t a : wf_signature sg ->
  wf_context sg ctx -> typing sg ctx t a -> strongly_normalizing t.
Proof.
  intros W CT T.
  destruct (typing_regular_representative _ _ _ _ W CT T) as [proper [C P]].
  apply (arity_strong_normalization (map type_shape sg) (map type_shape ctx) t (type_shape proper)).
  eapply typing_arity; [exact W|exact CT|eapply ty_conv; eauto|exact P].
Qed.

Theorem typing_evaluates sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx t a -> exists u, evaluates t u.
Proof.
  intros W CT T; apply strongly_normalizing_evaluates.
  eapply typing_strong_normalization; eauto.
Qed.

Theorem typing_normal_complete sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx t a -> exists u bound, forall fuel, bound <= fuel -> normal fuel t = Some u.
Proof.
  intros W CT T; apply strongly_normalizing_normal.
  eapply typing_strong_normalization; eauto.
Qed.

Theorem typed_equal_complete sg ctx a b ta tb : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx a ta -> typing sg ctx b tb -> conv a b ->
  eventually (fun fuel => equal fuel a b = true).
Proof.
  intros W CT A B C.
  destruct (typing_evaluates _ _ _ _ W CT A) as [u U].
  destruct (typing_evaluates _ _ _ _ W CT B) as [v V].
  eapply equal_complete_from_convertibility; eauto.
Qed.

Lemma evaluates_sort s : is_sort s -> evaluates s s.
Proof. intros [->| ->]; constructor. Qed.

Theorem typed_evaluates_sort sg ctx a ta s : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx a ta -> conv a s -> is_sort s -> evaluates a s.
Proof.
  intros W CT T C S; destruct (typing_evaluates _ _ _ _ W CT T) as [u U].
  pose proof (convertible_evaluations_agree _ _ _ _ C U (evaluates_sort _ S)) as E.
  subst u; exact U.
Qed.
