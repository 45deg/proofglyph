From Stdlib Require Import List Bool Lia.
From Tinyprover.Pa Require Import Syntax Kernel Program WellFormed Evaluation
  Substitution TypingSubstitution Confluence Generation Preservation Regularity
  Arity TypedNormalization.
Import ListNotations.

(** Lambda inference uses the simultaneously established validity of the
    inferred body type. [Kind] has no sort, so it cannot be a Pi codomain. *)
Fixpoint infer fuel sg ctx t : option term :=
  match fuel with
  | 0 => None
  | S n => match t with
    | tType => Some tKind
    | tKind => None
    | tVar i => a <- nth_error ctx i ;; Some (shift (S i) 0 a)
    | tConst i => nth_error sg i
    | tPi a b =>
      aty <- infer n sg ctx a ;;
      if equal n aty tType then
        bt <- infer n sg (a :: ctx) b ;; as_sort n bt
      else None
    | tLam a b =>
      aty <- infer n sg ctx a ;;
      if equal n aty tType then
        bt <- infer n sg (a :: ctx) b ;;
        match bt with tKind => None | _ => Some (tPi a bt) end
      else None
    | tApp f x =>
      ft <- infer n sg ctx f ;; p <- normal n ft ;;
      match p with
      | tPi a b => xt <- infer n sg ctx x ;;
        if equal n xt a then Some (instantiate b x) else None
      | _ => None
      end
    end
  end.

Theorem infer_sound fuel sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  infer fuel sg ctx t = Some a ->
  typing sg ctx t a /\ proper_type sg ctx a.
Proof.
  revert sg ctx t a; induction fuel as [|n IH]; intros sg ctx t typ W CT H; [discriminate|].
  destruct t as [| |i|i|a b|a b|f x]; cbn [infer] in H; unfold bind in H.
  - inversion H; subst; split; [constructor|left; reflexivity].
  - discriminate.
  - destruct (nth_error ctx i) as [a|] eqn:LOOK; try discriminate.
    inversion H; subst; split; [constructor; exact LOOK|right].
    exists tType; split; [eapply wf_context_lookup; eauto|left; reflexivity].
  - split; [constructor; exact H|right].
    apply sorted_type_any_context; [exact W|eapply wf_signature_lookup; eauto].
  - destruct (infer n sg ctx a) as [aty|] eqn:A; try discriminate.
    destruct (equal n aty tType) eqn:AE; try discriminate.
    destruct (infer n sg (a :: ctx) b) as [bt|] eqn:B; try discriminate.
    destruct (IH _ _ _ _ W CT A) as [AT AP].
    assert (DOMAIN : typing sg ctx a tType) by (eapply ty_conv; [exact AT|eapply equal_sound; exact AE]).
    destruct (IH _ _ _ _ W (wf_context_cons _ _ _ CT DOMAIN) B) as [BT BP].
    apply as_sort_sound in H as [C S]; split.
    + eapply ty_pi; [exact DOMAIN|eapply ty_conv; eauto|exact S].
    + apply sort_proper; exact S.
  - destruct (infer n sg ctx a) as [aty|] eqn:A; try discriminate.
    destruct (equal n aty tType) eqn:AE; try discriminate.
    destruct (infer n sg (a :: ctx) b) as [bt|] eqn:B; try discriminate.
    destruct (IH _ _ _ _ W CT A) as [AT AP].
    assert (DOMAIN : typing sg ctx a tType) by (eapply ty_conv; [exact AT|eapply equal_sound; exact AE]).
    destruct (IH _ _ _ _ W (wf_context_cons _ _ _ CT DOMAIN) B) as [BT [K|[s [SORT IS]]]].
    + subst bt; discriminate.
    + assert (OUT : typ = tPi a bt) by (destruct bt; inversion H; reflexivity).
      subst typ; assert (PI : typing sg ctx (tPi a bt) s) by (eapply ty_pi; eauto).
      split; [eapply ty_lam; eauto|right; exists s; auto].
  - destruct (infer n sg ctx f) as [ft|] eqn:F; try discriminate.
    destruct (normal n ft) as [p|] eqn:NF; try discriminate.
    destruct p as [| |i|i|a b|a b|g y]; try discriminate.
    cbn [bind] in H.
    destruct (infer n sg ctx x) as [xt|] eqn:X; try discriminate.
    destruct (equal n xt a) eqn:EQ; try discriminate.
    inversion H; subst typ.
    destruct (IH _ _ _ _ W CT F) as [FT FP].
    destruct (IH _ _ _ _ W CT X) as [XT XP].
    assert (ARG : typing sg ctx x a) by (eapply ty_conv; [exact XT|eapply equal_sound; exact EQ]).
    split.
    + eapply ty_app; [eapply ty_conv; [exact FT|eapply normal_sound; exact NF]|exact ARG].
    + right; destruct FP as [K|[s [T S]]].
      * subst ft; exfalso; eapply conv_pi_not_kind; apply cv_sym; eapply normal_sound; exact NF.
      * pose proof (normalization_preserves_type _ _ _ _ _ _ W T NF) as PI.
        apply typing_generation in PI; cbn [generates] in PI.
        destruct PI as [k [A [B [KS C]]]]; exists k; split; [|exact KS].
        rewrite <- (instantiate_sort k x KS); eapply typing_instantiate; eauto.
Qed.

Inductive synthesizes (sg : list term) : list term -> term -> term -> Prop :=
| ds_type : forall ctx, synthesizes sg ctx tType tKind
| ds_var : forall ctx n a, nth_error ctx n = Some a ->
    synthesizes sg ctx (tVar n) (shift (S n) 0 a)
| ds_const : forall ctx n a, nth_error sg n = Some a -> synthesizes sg ctx (tConst n) a
| ds_pi : forall ctx a b aty bt s,
    synthesizes sg ctx a aty -> evaluates aty tType ->
    synthesizes sg (a :: ctx) b bt -> evaluates bt s -> is_sort s ->
    synthesizes sg ctx (tPi a b) s
| ds_lam : forall ctx a b aty bt,
    synthesizes sg ctx a aty -> evaluates aty tType ->
    synthesizes sg (a :: ctx) b bt -> bt <> tKind ->
    synthesizes sg ctx (tLam a b) (tPi a bt)
| ds_app : forall ctx f x ft a b xt u,
    synthesizes sg ctx f ft -> evaluates ft (tPi a b) ->
    synthesizes sg ctx x xt -> evaluates xt u -> evaluates a u ->
    synthesizes sg ctx (tApp f x) (instantiate b x).

Theorem infer_complete sg ctx t a : synthesizes sg ctx t a ->
  eventually (fun fuel => infer fuel sg ctx t = Some a).
Proof.
  intros T; induction T.
  - exists 1; intros [|fuel] L; [lia|reflexivity].
  - exists 1; intros [|fuel] L; [lia|]; cbn [infer]; rewrite H; reflexivity.
  - exists 1; intros [|fuel] L; [lia|]; exact H.
  - pose proof (equal_complete _ _ _ H ev_type).
    pose proof (as_sort_complete _ _ H0 H1).
    next_fuel; cbn [infer]; unfold bind; rewrite_successes; rewrite_successes; reflexivity.
  - pose proof (equal_complete _ _ _ H ev_type).
    next_fuel; cbn [infer]; unfold bind; rewrite_successes; rewrite_successes.
    destruct bt; try reflexivity; contradiction.
  - pose proof (normal_complete _ _ H).
    pose proof (equal_complete _ _ _ H0 H1).
    next_fuel; cbn [infer]; unfold bind; rewrite_successes; rewrite_successes; reflexivity.
Qed.

Lemma synthesizes_sound sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  synthesizes sg ctx t a -> typing sg ctx t a /\ proper_type sg ctx a.
Proof.
  intros W CT T; destruct (infer_complete _ _ _ _ T) as [n N].
  eapply infer_sound; [exact W|exact CT|apply N; reflexivity].
Qed.

Lemma proper_evaluates sg ctx a : wf_signature sg -> wf_context sg ctx ->
  proper_type sg ctx a -> exists u, evaluates a u.
Proof.
  intros W CT [->|[s [T S]]]; [exists tKind; constructor|eapply typing_evaluates; eauto].
Qed.

Lemma proper_evaluates_sort sg ctx a s : wf_signature sg -> wf_context sg ctx ->
  proper_type sg ctx a -> conv a s -> is_sort s -> evaluates a s.
Proof.
  intros W CT P C S; destruct (proper_evaluates _ _ _ W CT P) as [u U].
  pose proof (convertible_evaluations_agree _ _ _ _ C U (evaluates_sort _ S)) as E.
  subst u; exact U.
Qed.

Lemma evaluates_conv t u : evaluates t u -> conv t u.
Proof. intros E; apply steps_conv; apply evaluates_steps; exact E. Qed.

Lemma normal_form_evaluates t : normal_form t -> evaluates t t.
Proof. intros N; induction N; eauto using evaluates. Qed.

Lemma evaluates_convertible_pi t u a b : evaluates t u -> conv t (tPi a b) ->
  exists c d, u = tPi c d /\ conv a c /\ conv b d.
Proof.
  intros E C.
  assert (CU : conv (tPi a b) u) by (eapply cv_trans; [apply cv_sym; exact C|apply evaluates_conv; exact E]).
  destruct (conv_joins _ _ CU) as [v [PV UV]].
  pose proof (steps_normal_form _ _ UV (evaluates_normal_form _ _ E)); subst v.
  destruct (steps_pi_inv _ _ PV _ _ eq_refl) as [c [d [U [A B]]]].
  exists c, d; repeat split; eauto using steps_conv.
Qed.

(** Completeness by structural induction on the input term. Normalization is
    supplied by the proved declarative strong-normalization theorem. *)
Theorem declarative_synthesizes sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx t a -> exists inferred,
    synthesizes sg ctx t inferred /\ conv inferred a.
Proof.
  intros W; revert ctx a; induction t as [| |n|n|a IHA b IHB|a IHA b IHB|f IHF x IHX];
    intros ctx typ CT T; apply typing_generation in T; cbn [generates] in T.
  - exists tKind; split; [constructor|exact T].
  - contradiction.
  - destruct T as [a [LOOK C]]; eexists; split; [constructor; exact LOOK|exact C].
  - destruct T as [a [LOOK C]]; exists a; split; [constructor; exact LOOK|exact C].
  - destruct T as [s [A [B [S C]]]].
    destruct (IHA _ _ CT A) as [aty [DA AC]].
    assert (CB : wf_context sg (a :: ctx)) by (constructor; assumption).
    destruct (IHB _ _ CB B) as [bt [DB BC]].
    destruct (synthesizes_sound _ _ _ _ W CT DA) as [_ AP].
    destruct (synthesizes_sound _ _ _ _ W CB DB) as [_ BP].
    exists s; split; [|exact C]. eapply ds_pi; [exact DA| |exact DB| |exact S].
    + exact (proper_evaluates_sort _ _ _ _ W CT AP AC (or_introl eq_refl)).
    + exact (proper_evaluates_sort _ _ _ _ W CB BP BC S).
  - destruct T as [bt [s [A [B [PI [S C]]]]]].
    destruct (IHA _ _ CT A) as [aty [DA AC]].
    assert (CB : wf_context sg (a :: ctx)) by (constructor; assumption).
    destruct (IHB _ _ CB B) as [inferred [DB BC]].
    destruct (synthesizes_sound _ _ _ _ W CT DA) as [_ AP].
    exists (tPi a inferred); split.
    + eapply ds_lam; [exact DA| |exact DB|].
      * exact (proper_evaluates_sort _ _ _ _ W CT AP AC (or_introl eq_refl)).
      * intros K; subst inferred.
        apply typing_generation in PI; cbn [generates] in PI.
        destruct PI as [k [_ [BT [KS _]]]].
        eapply sorted_not_conv_kind; [exact W|exists k; split; eassumption|apply cv_sym; exact BC].
    + eapply cv_trans; [apply cv_pi; [constructor|exact BC]|exact C].
  - destruct T as [a [b [F [X C]]]].
    destruct (IHF _ _ CT F) as [ft [DF FC]].
    destruct (IHX _ _ CT X) as [xt [DX XC]].
    destruct (synthesizes_sound _ _ _ _ W CT DF) as [_ FP].
    destruct (synthesizes_sound _ _ _ _ W CT DX) as [_ XP].
    destruct (proper_evaluates _ _ _ W CT FP) as [u U].
    destruct (evaluates_convertible_pi _ _ _ _ U FC) as [d [e [UE [AD BE]]]]; subst u.
    destruct (proper_evaluates _ _ _ W CT XP) as [v V].
    assert (D : evaluates d d).
    { apply normal_form_evaluates; pose proof (evaluates_normal_form _ _ U) as N; inversion N; assumption. }
    assert (XD : conv xt d) by (eapply cv_trans; eauto).
    pose proof (convertible_evaluations_agree _ _ _ _ XD V D) as VD; subst v.
    exists (instantiate e x); split.
    + eapply ds_app; eauto.
    + eapply cv_trans; [|exact C]. rewrite !instantiate_as_substitute.
      apply conv_substitute; apply cv_sym; exact BE.
Qed.

Theorem declarative_infer_complete sg ctx t a :
  wf_signature sg -> wf_context sg ctx -> typing sg ctx t a ->
  exists inferred bound, conv inferred a /\
    forall fuel, bound <= fuel -> infer fuel sg ctx t = Some inferred.
Proof.
  intros W CT T; destruct (declarative_synthesizes _ _ _ _ W CT T) as [b [B C]].
  destruct (infer_complete _ _ _ _ B) as [n N]; exists b, n; auto.
Qed.

Definition check fuel sg t a : bool :=
  match infer fuel sg [] a, infer fuel sg [] t with
  | Some aty, Some actual =>
    match as_sort fuel aty with Some _ => equal fuel actual a | None => false end
  | _, _ => false
  end.

Theorem check_sound fuel sg t a : wf_signature sg ->
  check fuel sg t a = true -> typing sg [] t a /\ sorted_type sg [] a.
Proof.
  intros W H; unfold check in H.
  destruct (infer fuel sg [] a) as [aty|] eqn:A; try discriminate.
  destruct (infer fuel sg [] t) as [actual|] eqn:T; try discriminate.
  destruct (as_sort fuel aty) as [s|] eqn:S; try discriminate.
  apply as_sort_sound in S as [C IS].
  destruct (infer_sound _ _ _ _ _ W (wf_context_nil _) A) as [AT _].
  destruct (infer_sound _ _ _ _ _ W (wf_context_nil _) T) as [TT _].
  split.
  - eapply ty_conv; [exact TT|eapply equal_sound; exact H].
  - exists s; split; [eapply ty_conv; eauto|exact IS].
Qed.

Theorem declarative_check_complete sg t a : wf_signature sg ->
  sorted_type sg [] a -> typing sg [] t a ->
  exists bound, forall fuel, bound <= fuel -> check fuel sg t a = true.
Proof.
  intros W [s [AT IS]] TT.
  destruct (declarative_synthesizes _ _ _ _ W (wf_context_nil _) AT) as [aty [A AC]].
  destruct (declarative_synthesizes _ _ _ _ W (wf_context_nil _) TT) as [actual [T TC]].
  destruct (synthesizes_sound _ _ _ _ W (wf_context_nil _) A) as [_ AP].
  destruct (synthesizes_sound _ _ _ _ W (wf_context_nil _) T) as [_ TP].
  pose proof (proper_evaluates_sort _ _ _ _ W (wf_context_nil _) AP AC IS) as ES.
  destruct (proper_evaluates _ _ _ W (wf_context_nil _) TP) as [u U].
  destruct (typing_evaluates _ _ _ _ W (wf_context_nil _) AT) as [v V].
  pose proof (infer_complete _ _ _ _ A).
  pose proof (infer_complete _ _ _ _ T).
  pose proof (as_sort_complete _ _ ES IS).
  pose proof (equal_complete_from_convertibility _ _ _ _ TC U V).
  combine_eventually.
  match goal with H : eventually _ |- _ =>
    destruct H as [n N]; exists n; intros fuel LE; specialize (N fuel LE) end.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  unfold check; rewrite_successes; reflexivity.
Qed.

Definition check_declaration fuel (allow : bool) sg d :=
  match d with
  | Assume a => if allow then
      match infer fuel sg [] a with
      | Some aty => match as_sort fuel aty with Some _ => true | None => false end
      | None => false end else false
  | Prove a t => check fuel sg t a
  end.

Fixpoint check_program fuel allow sg ds : option (list term) :=
  match ds with
  | [] => Some sg
  | d :: rest => if check_declaration fuel allow sg d then
      check_program fuel allow (sg ++ [declared_type d]) rest else None
  end.

Theorem check_declaration_sound fuel allow sg d : wf_signature sg ->
  check_declaration fuel allow sg d = true -> valid_declaration sg d.
Proof.
  intros W H; destruct d as [a|a t]; cbn [check_declaration] in H.
  - destruct allow; try discriminate.
    destruct (infer fuel sg [] a) as [aty|] eqn:A; try discriminate.
    destruct (as_sort fuel aty) as [s|] eqn:S; try discriminate.
    destruct (infer_sound _ _ _ _ _ W (wf_context_nil _) A) as [AT _].
    apply as_sort_sound in S as [C IS].
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
    destruct (declarative_synthesizes _ _ _ _ W (wf_context_nil _) AT) as [aty [A AC]].
    destruct (synthesizes_sound _ _ _ _ W (wf_context_nil _) A) as [_ AP].
    pose proof (proper_evaluates_sort _ _ _ _ W (wf_context_nil _) AP AC IS) as ES.
    pose proof (infer_complete _ _ _ _ A).
    pose proof (as_sort_complete _ _ ES IS).
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
  | context [normal ?k ?x] =>
      let E := fresh "E" in destruct (normal k x) eqn:E; try discriminate;
      try (rewrite (normal_monotone _ _ _ _ LE E))
  | context [if equal ?k ?x ?y then _ else _] =>
      let E := fresh "E" in destruct (equal k x y) eqn:E; try discriminate;
      try (rewrite (equal_monotone _ _ _ _ LE E))
  end.
  - eapply as_sort_monotone; eauto.
  - exact H.
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
    rewrite (infer_monotone _ _ _ _ _ _ L A), (as_sort_monotone _ _ _ _ L S); reflexivity.
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
