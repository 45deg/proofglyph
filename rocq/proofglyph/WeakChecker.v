From Stdlib Require Import List Bool Lia.
From Proofglyph.Language Require Import WeakNormalization WeakEvaluation Evaluation
  WellFormed Regularity TypedNormalization Arity.
From Proofglyph.Language Require Export WeakCheckerImpl.
Import ListNotations.

Theorem infer_relation fuel sg ctx t a :
  infer fuel sg ctx t = Some a -> weak_infer sg ctx t a.
Proof.
  revert sg ctx t a; induction fuel as [|n IH]; intros sg ctx t typ H; [discriminate|].
  destruct t as [| |i|i|a b|a b|f x]; cbn [infer bind] in H.
  - inversion H; constructor.
  - discriminate.
  - destruct (nth_error ctx i) eqn:A; try discriminate; inversion H; subst; constructor; exact A.
  - constructor; exact H.
  - destruct (infer n sg ctx a) as [aty|] eqn:A; try discriminate; cbn [bind] in H.
    destruct (w_as_sort n aty) as [s|] eqn:S; try discriminate; destruct s; try discriminate.
    destruct (infer n sg (a :: ctx) b) as [bt|] eqn:B; try discriminate; cbn [bind] in H.
    eapply wi_pi; [eapply IH; exact A|eapply w_as_sort_relation; exact S|
      eapply IH; exact B|eapply w_as_sort_relation; exact H].
  - destruct (infer n sg ctx a) as [aty|] eqn:A; try discriminate; cbn [bind] in H.
    destruct (w_as_sort n aty) as [s|] eqn:S; try discriminate; destruct s; try discriminate.
    destruct (infer n sg (a :: ctx) b) as [bt|] eqn:B; try discriminate; cbn [bind] in H.
    destruct bt; try discriminate; inversion H; subst;
      solve [eapply wi_lam; [eapply IH; exact A|eapply w_as_sort_relation; exact S|
        eapply IH; exact B|discriminate]].
  - destruct (infer n sg ctx f) as [ft|] eqn:F; try discriminate; cbn [bind] in H.
    destruct (whnf n ft) as [p|] eqn:P; try discriminate; cbn [bind] in H.
    destruct p; try discriminate; cbn [bind] in H.
    destruct (infer n sg ctx x) as [xt|] eqn:X; try discriminate; cbn [bind] in H.
    destruct (w_equal n xt p1) eqn:E; try discriminate; inversion H; subst.
    eapply wi_app; [eapply IH; exact F|eapply whnf_relation; exact P|
      eapply IH; exact X|eapply w_equal_relation; exact E].
Qed.

Theorem infer_sound fuel sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  infer fuel sg ctx t = Some a -> typing sg ctx t a /\ proper_type sg ctx a.
Proof. intros W CT H; apply weak_infer_sound; [exact W|exact CT|eapply infer_relation; exact H]. Qed.

Theorem infer_complete sg ctx t a : weak_infer sg ctx t a ->
  eventually (fun fuel => infer fuel sg ctx t = Some a).
Proof.
  intros T; induction T.
  - exists 1; intros [|fuel] L; [lia|reflexivity].
  - exists 1; intros [|fuel] L; [lia|]; cbn [infer]; rewrite H; reflexivity.
  - exists 1; intros [|fuel] L; [lia|]; exact H.
  - pose proof (w_as_sort_complete _ _ H); pose proof (w_as_sort_complete _ _ H0).
    next_fuel; cbn [infer]; rewrite_successes; reflexivity.
  - pose proof (w_as_sort_complete _ _ H).
    next_fuel; cbn [infer]; rewrite_successes.
    destruct bt; try reflexivity; contradiction.
  - pose proof (whnf_complete _ _ H); pose proof (w_equal_complete _ _ H0).
    next_fuel; cbn [infer]; rewrite_successes; reflexivity.
Qed.

Theorem declarative_infer_complete sg ctx t a :
  wf_signature sg -> wf_context sg ctx -> typing sg ctx t a ->
  exists inferred bound, conv inferred a /\
    forall fuel, bound <= fuel -> infer fuel sg ctx t = Some inferred.
Proof.
  intros W CT T; destruct (declarative_weak_infer _ _ _ _ W CT T) as [b [B C]].
  destruct (infer_complete _ _ _ _ B) as [n N]; exists b, n; auto.
Qed.

Theorem check_relation fuel sg t a : check fuel sg t a = true -> weak_check sg t a.
Proof.
  unfold check; destruct (infer fuel sg [] a) as [aty|] eqn:A; try discriminate.
  destruct (infer fuel sg [] t) as [actual|] eqn:T; try discriminate.
  destruct (w_as_sort fuel aty) as [s|] eqn:S; try discriminate; intros E.
  exists aty, actual, s; repeat split.
  - eapply infer_relation; exact A.
  - exact (proj1 (w_as_sort_relation _ _ _ S)).
  - exact (proj2 (w_as_sort_relation _ _ _ S)).
  - eapply infer_relation; exact T.
  - eapply w_equal_relation; exact E.
Qed.

Theorem check_sound fuel sg t a : wf_signature sg ->
  check fuel sg t a = true -> typing sg [] t a /\ sorted_type sg [] a.
Proof. intros W H; apply weak_check_sound; [exact W|eapply check_relation; exact H]. Qed.

Theorem check_complete sg t a : weak_check sg t a ->
  eventually (fun fuel => check fuel sg t a = true).
Proof.
  intros [aty [actual [s [A [S [T E]]]]]].
  pose proof (infer_complete _ _ _ _ A); pose proof (infer_complete _ _ _ _ T).
  pose proof (w_as_sort_complete _ _ S); pose proof (w_equal_complete _ _ E).
  combine_eventually.
  match goal with H : eventually _ |- _ => destruct H as [n N] end.
  exists n; intros fuel LE; specialize (N fuel LE).
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold check; rewrite_successes; reflexivity.
Qed.

Theorem declarative_check_complete sg t a : wf_signature sg ->
  sorted_type sg [] a -> typing sg [] t a ->
  exists bound, forall fuel, bound <= fuel -> check fuel sg t a = true.
Proof.
  intros W [s [AT IS]] TT.
  destruct (declarative_weak_infer _ _ _ _ W (wf_context_nil _) AT) as [aty [A AC]].
  destruct (declarative_weak_infer _ _ _ _ W (wf_context_nil _) TT) as [actual [T TC]].
  destruct (weak_infer_sound _ _ _ _ W (wf_context_nil _) A) as [_ AP].
  destruct (weak_infer_sound _ _ _ _ W (wf_context_nil _) T) as [_ TP].
  apply check_complete; exists aty, actual, s; repeat split; try assumption.
  - exact (proj1 (proper_weak_sort _ _ _ _ W (wf_context_nil _) AP AC IS)).
  - apply weak_equal_complete.
    + eapply proper_sn; eauto; constructor.
    + eapply typing_strong_normalization; eauto; constructor.
    + exact TC.
Qed.
Theorem check_declaration_sound fuel allow sg d : wf_signature sg ->
  check_declaration fuel allow sg d = true -> valid_declaration sg d.
Proof.
  intros W H; destruct d as [a|a t]; cbn [check_declaration] in H.
  - destruct allow; try discriminate.
    destruct (infer fuel sg [] a) as [aty|] eqn:A; try discriminate.
    destruct (w_as_sort fuel aty) as [s|] eqn:S; try discriminate.
    destruct (infer_sound _ _ _ _ _ W (wf_context_nil _) A) as [AT _].
    apply w_as_sort_sound in S as [C IS].
    split; [exists s; split; [eapply ty_conv; eauto|exact IS]|exact I].
  - destruct (check_sound _ _ _ _ W H) as [T A]; split; assumption.
Qed.

Theorem check_program_sound fuel allow sg ds final : wf_signature sg ->
  check_program fuel allow sg ds = Some final -> valid_program sg ds final.
Proof.
  revert sg; induction ds as [|d ds IH]; intros sg W H; cbn [check_program] in H.
  - inversion H; constructor.
  - destruct (check_declaration fuel allow sg d) eqn:D; try discriminate.
    pose proof (check_declaration_sound _ _ _ _ W D) as VD.
    constructor; [exact VD|apply IH; [eapply valid_declaration_extends_wf; eauto|exact H]].
Qed.

Theorem accepted_program_wf fuel allow sg ds final : wf_signature sg ->
  check_program fuel allow sg ds = Some final -> wf_signature final.
Proof.
  intros W H; eapply valid_program_preserves_wf; [exact W|].
  eapply check_program_sound; eauto.
Qed.

Theorem check_program_no_axioms fuel sg ds final :
  check_program fuel false sg ds = Some final -> permitted_declarations false ds.
Proof.
  revert sg; induction ds as [|d ds IH]; intros sg H; [constructor|].
  cbn [check_program] in H.
  destruct d as [a|a t]; cbn [check_declaration] in H; [discriminate|].
  destruct (check fuel sg t a) eqn:T; try discriminate.
  constructor; [exact I|eapply IH; exact H].
Qed.

Lemma declarative_declaration_complete allow sg d : wf_signature sg ->
  (match d with Assume _ => allow = true | Prove _ _ => True end) ->
  valid_declaration sg d ->
  eventually (fun fuel => check_declaration fuel allow sg d = true).
Proof.
  intros W POLICY VALID; destruct d as [a|a t]; destruct VALID as [[s [AT IS]] PROOF]; cbn [declared_type] in AT.
  - subst allow.
    destruct (declarative_weak_infer _ _ _ _ W (wf_context_nil _) AT) as [aty [A AC]].
    destruct (weak_infer_sound _ _ _ _ W (wf_context_nil _) A) as [_ AP].
    pose proof (proper_weak_sort _ _ _ _ W (wf_context_nil _) AP AC IS) as ES.
    pose proof (infer_complete _ _ _ _ A).
    pose proof (w_as_sort_complete _ _ ES).
    combine_eventually.
    match goal with H : eventually _ |- _ =>
      destruct H as [n N]; exists n; intros fuel LE; specialize (N fuel LE) end.
    destruct N; cbn [check_declaration]; rewrite_successes; reflexivity.
  - apply declarative_check_complete; [exact W|exists s; auto|exact PROOF].
Qed.

(** Declarative completeness for the executable checker. The assumptions say
    nothing about execution, normalization, fuel, or consistency of axioms. *)
Theorem declarative_program_complete allow sg ds final :
  wf_signature sg -> permitted_declarations allow ds -> valid_program sg ds final ->
  exists bound, forall fuel, bound <= fuel -> check_program fuel allow sg ds = Some final.
Proof.
  intros W POLICY VALID; revert W POLICY; induction VALID; intros W POLICY.
  - exists 0; reflexivity.
  - inversion POLICY; subst.
    pose proof (declarative_declaration_complete _ _ _ W H2 H) as D.
    assert (WN : wf_signature (sg ++ [declared_type d])) by (eapply valid_declaration_extends_wf; eauto).
    destruct (eventually_and _ _ D (IHVALID WN H3)) as [n N].
    exists n; intros fuel LE; destruct (N fuel LE) as [HD HT].
    cbn [check_program]; rewrite HD; exact HT.
Qed.

Corollary empty_signature_program_complete allow ds final :
  permitted_declarations allow ds -> valid_program [] ds final ->
  exists bound, forall fuel, bound <= fuel -> check_program fuel allow [] ds = Some final.
Proof. apply declarative_program_complete; constructor. Qed.

Theorem program_correct allow sg ds final : wf_signature sg ->
  ((exists fuel, check_program fuel allow sg ds = Some final) <->
   permitted_declarations allow ds /\ valid_program sg ds final).
Proof.
  intros W; split.
  - intros [fuel H]; split.
    + destruct allow.
      * unfold permitted_declarations; apply Forall_forall; intros d IN; destruct d; auto.
      * eapply check_program_no_axioms; exact H.
    + eapply check_program_sound; eauto.
  - intros [P V]; destruct (declarative_program_complete _ _ _ _ W P V) as [n N].
    exists n; apply N; reflexivity.
Qed.

Theorem prelude_and_main_complete prelude sg main final :
  valid_program [] prelude sg -> permitted_declarations false main -> valid_program sg main final ->
  exists bound, forall fuel, bound <= fuel ->
    check_program fuel true [] prelude = Some sg /\
    check_program fuel false sg main = Some final.
Proof.
  intros PRE POLICY MAIN.
  assert (W : wf_signature sg) by (eapply valid_program_preserves_wf; [constructor|exact PRE]).
  assert (PP : permitted_declarations true prelude).
  { unfold permitted_declarations; apply Forall_forall; intros d IN; destruct d; auto. }
  apply eventually_and.
  - apply empty_signature_program_complete; assumption.
  - apply declarative_program_complete; assumption.
Qed.

Theorem infer_monotone n m sg ctx t a :
  n <= m -> infer n sg ctx t = Some a -> infer m sg ctx t = Some a.
Proof.
  revert m sg ctx t a; induction n as [|n IH]; intros m sg ctx t a L H; [discriminate|].
  destruct m as [|m]; [lia|]. assert (LE : n <= m) by lia.
  destruct t; cbn [infer] in *; unfold bind in *; try assumption.
  all: repeat match type of H with
  | context [infer ?k ?sigma ?gamma ?x] =>
      let E := fresh "E" in destruct (infer k sigma gamma x) eqn:E; try discriminate;
      try (rewrite (IH m _ _ _ _ LE E))
  | context [whnf ?k ?x] =>
      let E := fresh "E" in destruct (whnf k x) eqn:E; try discriminate;
      try (rewrite (whnf_monotone _ _ _ _ LE E))
  | context [w_as_sort ?k ?x] =>
      let E := fresh "E" in destruct (w_as_sort k x) eqn:E; try discriminate;
      try (rewrite (w_as_sort_monotone _ _ _ _ LE E))
  | context [if w_equal ?k ?x ?y then _ else _] =>
      let E := fresh "E" in destruct (w_equal k x y) eqn:E; try discriminate;
      try (rewrite (w_equal_monotone _ _ _ _ LE E))
  | context [match ?x with tType => _ | _ => _ end] => destruct x; try discriminate
  end; try exact H.
Qed.

Theorem check_monotone n m sg t a :
  n <= m -> check n sg t a = true -> check m sg t a = true.
Proof.
  intros L H; unfold check in *.
  destruct (infer n sg [] a) eqn:A; try discriminate.
  destruct (infer n sg [] t) eqn:T; try discriminate.
  destruct (w_as_sort n t0) eqn:S; try discriminate.
  rewrite (infer_monotone _ _ _ _ _ _ L A), (infer_monotone _ _ _ _ _ _ L T),
    (w_as_sort_monotone _ _ _ _ L S).
  eapply w_equal_monotone; eauto.
Qed.

Theorem declaration_monotone n m allow sg d :
  n <= m -> check_declaration n allow sg d = true ->
  check_declaration m allow sg d = true.
Proof.
  intros L H; destruct d; cbn [check_declaration] in *.
  - destruct allow; try discriminate.
    destruct (infer n sg [] a) eqn:A; try discriminate.
    destruct (w_as_sort n t) eqn:S; try discriminate.
    rewrite (infer_monotone _ _ _ _ _ _ L A), (w_as_sort_monotone _ _ _ _ L S); reflexivity.
  - eapply check_monotone; eauto.
Qed.

Theorem program_monotone n m allow sg ds final :
  n <= m -> check_program n allow sg ds = Some final ->
  check_program m allow sg ds = Some final.
Proof.
  intros L; revert sg; induction ds as [|d ds IH]; intros sg H;
    cbn [check_program] in *; [exact H|].
  destruct (check_declaration n allow sg d) eqn:E; try discriminate.
  rewrite (declaration_monotone _ _ _ _ _ L E); apply IH; exact H.
Qed.

Theorem prelude_and_main_sound fuel prelude sg main final :
  check_program fuel true [] prelude = Some sg ->
  check_program fuel false sg main = Some final ->
  valid_program [] prelude sg /\ valid_program sg main final /\
    permitted_declarations false main /\ wf_signature final.
Proof.
  intros PRE MAIN.
  assert (EMPTY : wf_signature []) by constructor.
  pose proof (accepted_program_wf _ _ _ _ _ EMPTY PRE) as W.
  repeat split.
  - eapply check_program_sound; eauto.
  - eapply check_program_sound; eauto.
  - eapply check_program_no_axioms; eauto.
  - eapply accepted_program_wf; eauto.
Qed.
