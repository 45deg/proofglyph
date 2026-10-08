From Stdlib Require Import List.
From Tinyprover.Pa Require Import Syntax Kernel WellFormed Evaluation Confluence
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

Lemma evaluates_sort s : is_sort s -> evaluates s s.
Proof. intros [->| ->]; constructor. Qed.
