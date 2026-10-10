From Stdlib Require Import List Bool PeanoNat Lia.
From Proofglyph.Language Require Import CacheTable WeakChecker WellFormed Evaluation.
From Proofglyph.Language Require Export CachedCheckerImpl.
Import ListNotations.

Definition cache_valid sg (cache : inference_table) :=
  table_valid (fun key value =>
    WeakCheckerImpl.infer (fst value) sg (fst key) (snd key) = Some (snd value)) cache.
Definition computation_valid sg expected (result : option (term * inference_table)) :=
  match result with
  | Some (a, next) => expected = Some a /\ cache_valid sg next
  | None => expected = None end.

Lemma empty_cache_valid sg : cache_valid sg (table_empty tt).
Proof. apply table_empty_valid. Qed.

Lemma memoize_correct fuel sg ctx t cache compute : cache_valid sg cache ->
  computation_valid sg (WeakCheckerImpl.infer fuel sg ctx t) (compute cache) ->
  computation_valid sg (WeakCheckerImpl.infer fuel sg ctx t)
    (memoize fuel (ctx, t) cache compute).
Proof.
  intros VALID COMPUTE.
  assert (FRESH : computation_valid sg (WeakCheckerImpl.infer fuel sg ctx t)
    (result <- compute cache ;; let '(a, next) := result in
      Some (a, table_insert (ctx, t) (fuel, a) next))).
  { destruct (compute cache) as [[a next]|]; cbn [bind computation_valid] in *; [|exact COMPUTE].
    destruct COMPUTE as [E V]; split; [exact E|].
    apply table_insert_valid; [exact V|exact E]. }
  unfold memoize.
  destruct (table_lookup cache_key_eq (ctx, t) cache) as [[bound a]|] eqn:LOOK;
    [|exact FRESH].
  destruct (bound <=? fuel) eqn:LE; [|exact FRESH].
  split; [|exact VALID].
  apply Nat.leb_le in LE.
  pose proof (table_lookup_valid _ _ _ _ _ VALID LOOK) as H.
  cbn in H; eapply WeakChecker.infer_monotone; eauto.
Qed.

Theorem infer_correct fuel sg ctx t cache : cache_valid sg cache ->
  computation_valid sg (WeakCheckerImpl.infer fuel sg ctx t) (infer fuel sg ctx t cache).
Proof.
  revert sg ctx t cache; induction fuel as [|n IH]; intros sg ctx t cache VALID;
    [reflexivity|].
  cbn [infer]; apply memoize_correct; [exact VALID|].
  destruct t as [| |i|i|a b|a b|f x]; cbn [WeakCheckerImpl.infer bind computation_valid].
  - split; [reflexivity|exact VALID].
  - reflexivity.
  - destruct (nth_error ctx i); cbn [bind computation_valid]; auto.
  - destruct (nth_error sg i); cbn [bind computation_valid]; auto.
  - pose proof (IH sg ctx a cache VALID) as A.
    destruct (infer n sg ctx a cache) as [[aty next]|] eqn:CA;
      cbn [computation_valid] in A; [destruct A as [A VA]|]; rewrite A; cbn [bind computation_valid]; [|reflexivity].
    destruct (w_as_sort n aty) as [s|]; [destruct s|]; try reflexivity.
    pose proof (IH sg (a :: ctx) b next VA) as B.
    destruct (infer n sg (a :: ctx) b next) as [[bt final]|];
      cbn [computation_valid] in B; [destruct B as [B VB]|]; rewrite B; cbn [bind computation_valid]; [|reflexivity].
    destruct (w_as_sort n bt); cbn [bind computation_valid]; auto.
  - pose proof (IH sg ctx a cache VALID) as A.
    destruct (infer n sg ctx a cache) as [[aty next]|];
      cbn [computation_valid] in A; [destruct A as [A VA]|]; rewrite A; cbn [bind computation_valid]; [|reflexivity].
    destruct (w_as_sort n aty) as [s|]; [destruct s|]; try reflexivity.
    pose proof (IH sg (a :: ctx) b next VA) as B.
    destruct (infer n sg (a :: ctx) b next) as [[bt final]|];
      cbn [computation_valid] in B; [destruct B as [B VB]|]; rewrite B; cbn [bind computation_valid]; [|reflexivity].
    destruct bt; cbn [computation_valid]; auto.
  - pose proof (IH sg ctx f cache VALID) as F.
    destruct (infer n sg ctx f cache) as [[ft next]|];
      cbn [computation_valid] in F; [destruct F as [F VF]|]; rewrite F; cbn [bind computation_valid]; [|reflexivity].
    destruct (whnf n ft) as [p|]; [destruct p|]; cbn [bind]; try reflexivity.
    pose proof (IH sg ctx x next VF) as X.
    destruct (infer n sg ctx x next) as [[xt final]|];
      cbn [computation_valid] in X; [destruct X as [X VX]|]; rewrite X; cbn [bind computation_valid]; [|reflexivity].
    destruct (w_equal n xt p1); cbn [computation_valid]; auto.
Qed.

Theorem check_equivalent fuel sg t a : check fuel sg t a = WeakCheckerImpl.check fuel sg t a.
Proof.
  unfold check, WeakCheckerImpl.check.
  pose proof (infer_correct fuel sg [] a (table_empty tt) (empty_cache_valid sg)) as A.
  destruct (infer fuel sg [] a (table_empty tt)) as [[aty cache]|];
    cbn [computation_valid] in A; [destruct A as [A VA]|]; rewrite A; [|reflexivity].
  pose proof (infer_correct fuel sg [] t cache VA) as T.
  destruct (infer fuel sg [] t cache) as [[actual final]|];
    cbn [computation_valid] in T; [destruct T as [T VT]|]; rewrite T; reflexivity.
Qed.

Theorem declaration_equivalent fuel allow sg d :
  check_declaration fuel allow sg d = WeakCheckerImpl.check_declaration fuel allow sg d.
Proof.
  destruct d as [a|a t]; cbn [check_declaration WeakCheckerImpl.check_declaration]; [|apply check_equivalent].
  destruct allow; [|reflexivity].
  pose proof (infer_correct fuel sg [] a (table_empty tt) (empty_cache_valid sg)) as A.
  destruct (infer fuel sg [] a (table_empty tt)) as [[aty cache]|];
    cbn [computation_valid] in A; [destruct A as [A VA]|]; rewrite A; reflexivity.
Qed.

Theorem program_equivalent fuel allow sg ds :
  check_program fuel allow sg ds = WeakCheckerImpl.check_program fuel allow sg ds.
Proof.
  revert sg; induction ds; intros sg; cbn [check_program WeakCheckerImpl.check_program]; [reflexivity|].
  rewrite declaration_equivalent; destruct (WeakCheckerImpl.check_declaration fuel allow sg a);
    [apply IHds|reflexivity].
Qed.

Theorem check_sound fuel sg t a : wf_signature sg ->
  check fuel sg t a = true -> typing sg [] t a /\ sorted_type sg [] a.
Proof. setoid_rewrite check_equivalent; apply WeakChecker.check_sound. Qed.

Theorem declarative_check_complete sg t a : wf_signature sg ->
  sorted_type sg [] a -> typing sg [] t a ->
  exists bound, forall fuel, bound <= fuel -> check fuel sg t a = true.
Proof. setoid_rewrite check_equivalent; apply WeakChecker.declarative_check_complete. Qed.

Theorem check_declaration_sound fuel allow sg d : wf_signature sg ->
  check_declaration fuel allow sg d = true -> valid_declaration sg d.
Proof. setoid_rewrite declaration_equivalent; apply WeakChecker.check_declaration_sound. Qed.

Theorem check_program_sound fuel allow sg ds final : wf_signature sg ->
  check_program fuel allow sg ds = Some final -> valid_program sg ds final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.check_program_sound. Qed.

Theorem accepted_program_wf fuel allow sg ds final : wf_signature sg ->
  check_program fuel allow sg ds = Some final -> wf_signature final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.accepted_program_wf. Qed.

Theorem check_program_no_axioms fuel sg ds final :
  check_program fuel false sg ds = Some final -> permitted_declarations false ds.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.check_program_no_axioms. Qed.

Lemma declarative_declaration_complete allow sg d : wf_signature sg ->
  (match d with Assume _ => allow = true | Prove _ _ => True end) ->
  valid_declaration sg d ->
  eventually (fun fuel => check_declaration fuel allow sg d = true).
Proof. unfold eventually; setoid_rewrite declaration_equivalent; apply WeakChecker.declarative_declaration_complete. Qed.

Theorem declarative_program_complete allow sg ds final :
  wf_signature sg -> permitted_declarations allow ds -> valid_program sg ds final ->
  exists bound, forall fuel, bound <= fuel -> check_program fuel allow sg ds = Some final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.declarative_program_complete. Qed.

Corollary empty_signature_program_complete allow ds final :
  permitted_declarations allow ds -> valid_program [] ds final ->
  exists bound, forall fuel, bound <= fuel -> check_program fuel allow [] ds = Some final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.empty_signature_program_complete. Qed.

Theorem program_correct allow sg ds final : wf_signature sg ->
  ((exists fuel, check_program fuel allow sg ds = Some final) <->
   permitted_declarations allow ds /\ valid_program sg ds final).
Proof. setoid_rewrite program_equivalent; apply WeakChecker.program_correct. Qed.

Theorem prelude_and_main_complete prelude sg main final :
  valid_program [] prelude sg -> permitted_declarations false main -> valid_program sg main final ->
  exists bound, forall fuel, bound <= fuel ->
    check_program fuel true [] prelude = Some sg /\
    check_program fuel false sg main = Some final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.prelude_and_main_complete. Qed.

Theorem check_monotone n m sg t a :
  n <= m -> check n sg t a = true -> check m sg t a = true.
Proof. setoid_rewrite check_equivalent; apply WeakChecker.check_monotone. Qed.

Theorem declaration_monotone n m allow sg d :
  n <= m -> check_declaration n allow sg d = true ->
  check_declaration m allow sg d = true.
Proof. setoid_rewrite declaration_equivalent; apply WeakChecker.declaration_monotone. Qed.

Theorem program_monotone n m allow sg ds final :
  n <= m -> check_program n allow sg ds = Some final ->
  check_program m allow sg ds = Some final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.program_monotone. Qed.

Theorem prelude_and_main_sound fuel prelude sg main final :
  check_program fuel true [] prelude = Some sg ->
  check_program fuel false sg main = Some final ->
  valid_program [] prelude sg /\ valid_program sg main final /\
    permitted_declarations false main /\ wf_signature final.
Proof. setoid_rewrite program_equivalent; apply WeakChecker.prelude_and_main_sound. Qed.
