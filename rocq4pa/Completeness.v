From Stdlib Require Import List PeanoNat Lia.
From Rocq4pa Require Import Syntax Kernel Program WellFormed.
Import ListNotations.

(** Successful computations are stable when the depth budget increases. *)
Theorem normal_monotone n m t u :
  n <= m -> normal n t = Some u -> normal m t = Some u.
Proof.
  revert m t u; induction n as [|n IH]; intros m t u LE H; [discriminate|].
  destruct m as [|m]; [lia|]. assert (L : n <= m) by lia.
  destruct t; cbn [normal] in *; unfold bind in *;
    repeat match type of H with
    | context [normal ?k ?x] =>
        let E := fresh "E" in destruct (normal k x) eqn:E; try discriminate;
        try (rewrite (IH m _ _ L E))
    end; try assumption.
  all: match type of H with context [match ?x with tType => _ | _ => _ end] =>
    destruct x; try assumption end.
  eapply IH; eauto.
Qed.

Theorem equal_monotone n m a b :
  n <= m -> equal n a b = true -> equal m a b = true.
Proof.
  intros L H; unfold equal in *.
  destruct (normal n a) eqn:A; try discriminate.
  destruct (normal n b) eqn:B; try discriminate.
  rewrite (normal_monotone _ _ _ _ L A), (normal_monotone _ _ _ _ L B); exact H.
Qed.

Theorem as_sort_monotone n m a s :
  n <= m -> as_sort n a = Some s -> as_sort m a = Some s.
Proof.
  intros L H; unfold as_sort, bind in *.
  destruct (normal n a) eqn:A; try discriminate.
  rewrite (normal_monotone _ _ _ _ L A); exact H.
Qed.

Theorem infer_monotone n m sg ctx t a :
  n <= m -> infer n sg ctx t = Some a -> infer m sg ctx t = Some a.
Proof.
  revert m sg ctx t a; induction n as [|n IH]; intros m sg ctx t a L H;
    [discriminate|].
  destruct m as [|m]; [lia|]. assert (LE : n <= m) by lia.
  destruct t; cbn [infer] in *; unfold bind in *; try assumption.
  all: repeat match type of H with
  | context [infer ?k ?sigma ?gamma ?x] =>
      let E := fresh "E" in destruct (infer k sigma gamma x) eqn:E; try discriminate;
      try (rewrite (IH m _ _ _ _ LE E))
  | context [normal ?k ?x] =>
      let E := fresh "E" in destruct (normal k x) eqn:E; try discriminate;
      try (rewrite (normal_monotone _ _ _ _ LE E))
  | context [if equal ?k ?x ?y then _ else _] =>
      let E := fresh "E" in destruct (equal k x y) eqn:E; try discriminate;
      try (rewrite (equal_monotone _ _ _ _ LE E))
  end.
  - eapply as_sort_monotone; eauto.
  - destruct (as_sort n t3) eqn:ES; try discriminate.
    rewrite (as_sort_monotone _ _ _ _ LE ES); exact H.
  - destruct t3; try discriminate;
      repeat match type of H with
      | context [if equal ?k ?x ?y then _ else _] =>
          let E := fresh "E" in destruct (equal k x y) eqn:E; try discriminate;
          rewrite (equal_monotone _ _ _ _ LE E)
      end; exact H.
  - destruct t0; discriminate.
Qed.

Theorem check_monotone n m sg t a :
  n <= m -> check n sg t a = true -> check m sg t a = true.
Proof.
  intros L H; unfold check in *.
  destruct (infer n sg [] a) eqn:A; try discriminate.
  destruct (infer n sg [] t) eqn:T; try discriminate.
  destruct (as_sort n t0) eqn:S; try discriminate.
  rewrite (infer_monotone _ _ _ _ _ _ L A), (infer_monotone _ _ _ _ _ _ L T),
    (as_sort_monotone _ _ _ _ L S).
  eapply equal_monotone; eauto.
Qed.

Theorem declaration_monotone n m allow sg d :
  n <= m -> check_declaration n allow sg d = true ->
  check_declaration m allow sg d = true.
Proof.
  intros L H; destruct d; cbn [check_declaration] in *.
  - destruct allow; try discriminate.
    destruct (infer n sg [] a) eqn:A; try discriminate.
    destruct (as_sort n t) eqn:S; try discriminate.
    rewrite (infer_monotone _ _ _ _ _ _ L A), (as_sort_monotone _ _ _ _ L S).
    reflexivity.
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

(** A bound works for EVERY larger fuel, rather than just one witness. *)
Definition eventually (P : nat -> Prop) := exists bound, forall fuel, bound <= fuel -> P fuel.

Lemma eventually_and P Q : eventually P -> eventually Q ->
  eventually (fun n => P n /\ Q n).
Proof.
  intros [p HP] [q HQ]; exists (Nat.max p q); intros n H; split;
    [apply HP|apply HQ]; lia.
Qed.

(** Fuel-free, finite big-step evaluation for this eager normalization strategy.
    This relation does not mention [normal] or existential fuel. *)
Inductive evaluates : term -> term -> Prop :=
| ev_type : evaluates tType tType
| ev_kind : evaluates tKind tKind
| ev_var : forall n, evaluates (tVar n) (tVar n)
| ev_const : forall n, evaluates (tConst n) (tConst n)
| ev_pi : forall a b a' b', evaluates a a' -> evaluates b b' ->
    evaluates (tPi a b) (tPi a' b')
| ev_lam : forall a b a' b', evaluates a a' -> evaluates b b' ->
    evaluates (tLam a b) (tLam a' b')
| ev_app : forall f x f' x', evaluates f f' -> evaluates x x' ->
    (forall a b, f' <> tLam a b) -> evaluates (tApp f x) (tApp f' x')
| ev_beta : forall f x a b x' u, evaluates f (tLam a b) -> evaluates x x' ->
    evaluates (instantiate b x') u -> evaluates (tApp f x) u.

Theorem normal_complete t u : evaluates t u ->
  eventually (fun fuel => normal fuel t = Some u).
Proof.
  intros H; induction H.
  all: try (exists 1; intros [|fuel] L; [lia|reflexivity]).
  - destruct (eventually_and _ _ IHevaluates1 IHevaluates2) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A B]. cbn [normal]; rewrite A; cbn [bind]; rewrite B; reflexivity.
  - destruct (eventually_and _ _ IHevaluates1 IHevaluates2) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A B]. cbn [normal]; rewrite A; cbn [bind]; rewrite B; reflexivity.
  - destruct (eventually_and _ _ IHevaluates1 IHevaluates2) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A B]. cbn [normal]; rewrite A; cbn [bind]; rewrite B.
    destruct f'; try reflexivity. exfalso; eapply H1; reflexivity.
  - destruct (eventually_and _ _ IHevaluates1
      (eventually_and _ _ IHevaluates2 IHevaluates3)) as [k HK].
    exists (S k); intros [|n] L; [lia|].
    destruct (HK n ltac:(lia)) as [A [B C]].
    cbn [normal]; rewrite A; cbn [bind]; rewrite B; exact C.
Qed.

Theorem equal_complete a b u : evaluates a u -> evaluates b u ->
  eventually (fun fuel => equal fuel a b = true).
Proof.
  intros A B.
  destruct (eventually_and _ _ (normal_complete _ _ A) (normal_complete _ _ B)) as [k HK].
  exists k; intros n L; destruct (HK n L) as [NA NB].
  unfold equal; rewrite NA, NB; destruct (term_eq_dec u u); congruence.
Qed.

Theorem as_sort_complete a s : evaluates a s -> is_sort s ->
  eventually (fun fuel => as_sort fuel a = Some s).
Proof.
  intros A S; destruct (normal_complete _ _ A) as [k HK].
  exists k; intros n L; unfold as_sort; rewrite (HK n L); cbn [bind].
  destruct S as [-> | ->]; reflexivity.
Qed.

(** Finite algorithmic derivations, with no fuel or calls to the checker.
    Completeness for this relation does NOT assert that every declarative
    [typing] derivation has such a finite derivation. *)
Inductive synthesizes (sg : list term) : list term -> term -> term -> Prop :=
| sy_type : forall ctx, synthesizes sg ctx tType tKind
| sy_var : forall ctx n a, nth_error ctx n = Some a ->
    synthesizes sg ctx (tVar n) (shift (S n) 0 a)
| sy_const : forall ctx n a, nth_error sg n = Some a ->
    synthesizes sg ctx (tConst n) a
| sy_pi : forall ctx a b aty bt s,
    synthesizes sg ctx a aty -> evaluates aty tType ->
    synthesizes sg (a :: ctx) b bt -> evaluates bt s -> is_sort s ->
    synthesizes sg ctx (tPi a b) s
| sy_lam : forall ctx a b aty bt pt s,
    synthesizes sg ctx a aty -> evaluates aty tType ->
    synthesizes sg (a :: ctx) b bt -> synthesizes sg ctx (tPi a bt) pt ->
    evaluates pt s -> is_sort s -> synthesizes sg ctx (tLam a b) (tPi a bt)
| sy_app : forall ctx f x ft a b xt u,
    synthesizes sg ctx f ft -> evaluates ft (tPi a b) ->
    synthesizes sg ctx x xt -> evaluates xt u -> evaluates a u ->
    synthesizes sg ctx (tApp f x) (instantiate b x).

Ltac combine_eventually :=
  repeat match goal with
  | H1 : eventually ?P, H2 : eventually ?Q |- _ =>
      let H := fresh "combined" in
      pose proof (eventually_and P Q H1 H2) as H; clear H1 H2
  end.

Ltac next_fuel :=
  combine_eventually;
  match goal with H : eventually _ |- _ =>
    let k := fresh "bound" in let HK := fresh "bounded" in
    destruct H as [k HK]; exists (S k);
    intros [|fuel] LE; [lia|]; specialize (HK fuel ltac:(lia));
    repeat match goal with H : _ /\ _ |- _ => destruct H end
  end.

Ltac rewrite_successes :=
  repeat match goal with H : ?x = Some ?v |- context [?x] => rewrite H; cbn [bind] end;
  repeat match goal with H : ?x = true |- context [?x] => rewrite H; cbn [bind] end.

Theorem infer_complete sg ctx t a : synthesizes sg ctx t a ->
  eventually (fun fuel => infer fuel sg ctx t = Some a).
Proof.
  intros H; induction H.
  - exists 1; intros [|fuel] L; [lia|reflexivity].
  - exists 1; intros [|fuel] L; [lia|]; cbn [infer]; rewrite H; reflexivity.
  - exists 1; intros [|fuel] L; [lia|]; exact H.
  - pose proof (equal_complete _ _ _ H0 ev_type).
    pose proof (as_sort_complete _ _ H2 H3).
    next_fuel; cbn [infer]; unfold bind; rewrite_successes; rewrite_successes; reflexivity.
  - pose proof (equal_complete _ _ _ H0 ev_type).
    pose proof (as_sort_complete _ _ H3 H4).
    next_fuel; cbn [infer]; unfold bind; rewrite_successes; rewrite_successes; reflexivity.
  - pose proof (normal_complete _ _ H0).
    pose proof (equal_complete _ _ _ H2 H3).
    next_fuel; cbn [infer]; unfold bind; rewrite_successes; rewrite_successes; reflexivity.
Qed.

Inductive checks (sg : list term) (t a : term) : Prop :=
| checks_intro : forall aty actual s u,
    synthesizes sg [] a aty -> evaluates aty s -> is_sort s ->
    synthesizes sg [] t actual -> evaluates actual u -> evaluates a u -> checks sg t a.

Theorem check_complete sg t a : checks sg t a ->
  eventually (fun fuel => check fuel sg t a = true).
Proof.
  intros [aty actual s u A S IS T N1 N2].
  pose proof (infer_complete _ _ _ _ A).
  pose proof (infer_complete _ _ _ _ T).
  pose proof (as_sort_complete _ _ S IS).
  pose proof (equal_complete _ _ _ N1 N2).
  combine_eventually.
  match goal with H : eventually _ |- _ =>
    destruct H as [k HK]; exists k; intros fuel L; specialize (HK fuel L) end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold check; rewrite_successes; reflexivity.
Qed.

Inductive declaration_derivation (allow : bool) (sg : list term) : declaration -> Prop :=
| dd_assume : forall a aty s, allow = true -> synthesizes sg [] a aty ->
    evaluates aty s -> is_sort s -> declaration_derivation allow sg (Assume a)
| dd_prove : forall a t, checks sg t a -> declaration_derivation allow sg (Prove a t).

Theorem declaration_complete allow sg d : declaration_derivation allow sg d ->
  eventually (fun fuel => check_declaration fuel allow sg d = true).
Proof.
  intros H; destruct H.
  - subst allow. pose proof (infer_complete _ _ _ _ H0).
    pose proof (as_sort_complete _ _ H1 H2).
    combine_eventually.
    match goal with H : eventually _ |- _ =>
      destruct H as [k HK]; exists k; intros fuel L; specialize (HK fuel L) end.
    destruct HK; cbn [check_declaration]; rewrite_successes; reflexivity.
  - apply check_complete in H; exact H.
Qed.

Inductive program_derivation (allow : bool) : list term -> list declaration -> list term -> Prop :=
| pd_nil : forall sg, program_derivation allow sg [] sg
| pd_cons : forall sg d ds final, declaration_derivation allow sg d ->
    program_derivation allow (sg ++ [declared_type d]) ds final ->
    program_derivation allow sg (d :: ds) final.

Theorem program_complete allow sg ds final : program_derivation allow sg ds final ->
  exists bound, forall fuel, bound <= fuel -> check_program fuel allow sg ds = Some final.
Proof.
  intros H; induction H.
  - exists 0; reflexivity.
  - pose proof (declaration_complete _ _ _ H) as D.
    destruct (eventually_and _ _ D IHprogram_derivation) as [k HK].
    exists k; intros fuel L; destruct (HK fuel L) as [HD HT].
    cbn [check_program]; rewrite HD; exact HT.
Qed.

Theorem normal_evaluates fuel t u : normal fuel t = Some u -> evaluates t u.
Proof.
  revert t u; induction fuel as [|n IH]; intros t u H; [discriminate|].
  destruct t as [| |i|i|a b|a b|f x]; cbn [normal bind] in H.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - split_options; inversion H; subst; constructor; eauto.
  - split_options; inversion H; subst; constructor; eauto.
  - destruct (normal n f) as [f'|] eqn:F; try discriminate.
    cbn [bind] in H.
    destruct (normal n x) as [x'|] eqn:X; try discriminate.
    cbn [bind] in H.
    pose proof (IH _ _ F) as EF.
    pose proof (IH _ _ X) as EX.
    destruct f'; try (inversion H; subst; apply ev_app; auto; intros; discriminate).
    eapply ev_beta; eauto.
Qed.

Theorem normalization_iff t u :
  evaluates t u <-> exists fuel, normal fuel t = Some u.
Proof.
  split.
  - intros H; destruct (normal_complete _ _ H) as [k HK]; exists k; apply HK; reflexivity.
  - intros [fuel H]; eapply normal_evaluates; eauto.
Qed.

Theorem synthesizes_sound sg ctx t a : synthesizes sg ctx t a -> typing sg ctx t a.
Proof.
  intros H; destruct (infer_complete _ _ _ _ H) as [k HK].
  eapply infer_sound; apply HK; reflexivity.
Qed.

Theorem program_derivation_sound allow sg ds final :
  program_derivation allow sg ds final -> valid_program sg ds final.
Proof.
  intros H; destruct (program_complete _ _ _ _ H) as [k HK].
  eapply check_program_sound; apply HK; reflexivity.
Qed.

(** The missing bridge is restricted to well-formed signatures and permitted
    declarations. valid_program already requires sorted declaration types.
    This is a proposition, not an axiom or an admitted theorem. *)
Definition declarative_bridge : Prop := forall allow sg ds final,
  wf_signature sg -> permitted_declarations allow ds ->
  valid_program sg ds final -> program_derivation allow sg ds final.

(** Term-level completeness has a separate sorted-target premise: raw
    ty_conv alone may assign an untypable beta-expanded target to a term. *)
Definition declarative_check_completeness : Prop := forall sg t a,
  wf_signature sg -> sorted_type sg [] a -> typing sg [] t a ->
  exists bound, forall fuel, bound <= fuel -> check fuel sg t a = true.

(** Inference returns a representative of the beta-equivalence class of A,
    not necessarily A itself. tType : tKind is included here. *)
Definition declarative_infer_completeness : Prop := forall sg ctx t a,
  wf_signature sg -> wf_context sg ctx -> typing sg ctx t a ->
  exists inferred bound, conv inferred a /\
    forall fuel, bound <= fuel -> infer fuel sg ctx t = Some inferred.

Theorem declarative_complete_if_bridge : declarative_bridge ->
  forall allow sg ds final,
  wf_signature sg -> permitted_declarations allow ds -> valid_program sg ds final ->
  exists bound, forall fuel, bound <= fuel -> check_program fuel allow sg ds = Some final.
Proof.
  intros bridge allow sg ds final W P H; apply program_complete; apply bridge; assumption.
Qed.
