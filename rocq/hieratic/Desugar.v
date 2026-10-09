From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Tinyprover.Hieratic Require Export DesugarImpl.

Lemma products_sound ps b : products ps b (bind_products ps b).
Proof. induction ps as [|[x a] ps IH]; cbn; constructor; assumption. Qed.
Lemma lambdas_sound ps b : lambdas ps b (bind_lambdas ps b).
Proof. induction ps as [|[x a] ps IH]; cbn; constructor; assumption. Qed.
Lemma products_complete ps b out : products ps b out -> bind_products ps b = out.
Proof. intros H; induction H; cbn; congruence. Qed.
Lemma lambdas_complete ps b out : lambdas ps b out -> bind_lambdas ps b = out.
Proof. intros H; induction H; cbn; congruence. Qed.

Lemma desugar_sound_mutual :
  (forall e, expands e (desugar e)) /\
  (forall ps, expands_parameters ps (desugar_parameters ps)).
Proof.
  apply raw_mutind; cbn; intros; econstructor; eauto using products_sound, lambdas_sound.
Qed.

Lemma desugar_complete_mutual :
  (forall e out, expands e out -> desugar e = out) /\
  (forall ps out, expands_parameters ps out -> desugar_parameters ps = out).
Proof.
  apply expansion_mutind; cbn; intros; subst; eauto using products_complete, lambdas_complete.
Qed.

Theorem desugar_correct e out : desugar e = out <-> expands e out.
Proof.
  split; [intros <-; apply desugar_sound_mutual|apply desugar_complete_mutual].
Qed.

Theorem desugar_parameters_correct ps out :
  desugar_parameters ps = out <-> expands_parameters ps out.
Proof.
  split; [intros <-; apply desugar_sound_mutual|apply desugar_complete_mutual].
Qed.

(** Splitting a group into adjacent groups preserves its sequential meaning,
    even when an earlier name shadows a free name in the annotation. *)
Theorem split_parameter_group x y xs a rest :
  desugar_parameters (PGroup x (y :: xs) a rest) =
  desugar_parameters (PGroup x [] a (PGroup y xs a rest)).
Proof. reflexivity. Qed.

Lemma desugar_declaration_sound d : expands_declaration d (desugar_declaration d).
Proof.
  destruct d as [n a [b|]]; cbn; constructor; apply desugar_sound_mutual.
Qed.
Lemma desugar_declaration_complete d out :
  expands_declaration d out -> desugar_declaration d = out.
Proof.
  intros H; destruct H; unfold desugar_declaration; cbn.
  - rewrite (proj2 (desugar_correct _ _) H); reflexivity.
  - rewrite (proj2 (desugar_correct _ _) H), (proj2 (desugar_correct _ _) H0); reflexivity.
Qed.

Theorem desugar_program_correct src out : desugar_program src = out <-> expands_program src out.
Proof.
  split.
  - intros <-; induction src; cbn; constructor; auto using desugar_declaration_sound.
  - intros H; induction H; cbn; [reflexivity|].
    rewrite (desugar_declaration_complete _ _ H), IHForall2; reflexivity.
Qed.

Theorem desugar_names src : map decl_name (desugar_program src) = map raw_name src.
Proof. induction src; cbn; congruence. Qed.

Theorem desugar_kinds src : map is_assumption (desugar_program src) =
  map (fun d => match raw_body d with None => true | Some _ => false end) src.
Proof.
  induction src as [|[n a [b|]] src IH]; cbn; try rewrite IH; reflexivity.
Qed.
