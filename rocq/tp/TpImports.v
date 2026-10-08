From Stdlib Require Import List String Arith Lia.
From Tinyprover.Tp Require Export TpImportsImpl.
Import ListNotations.
Open Scope list_scope.

Lemma contains_file_correct path paths : contains_file path paths = true <-> In path paths.
Proof.
  unfold contains_file; rewrite existsb_exists; split.
  - intros [p [I E]]; apply String.eqb_eq in E; subst; exact I.
  - intros I; exists path; split; [exact I|apply String.eqb_refl].
Qed.
Lemma contains_file_false path paths : contains_file path paths = false <-> ~ In path paths.
Proof. rewrite <- contains_file_correct; destruct (contains_file path paths); intuition discriminate. Qed.
Lemma lookup_file_correct path files items : lookup_file path files = Some items <-> file_entry path files items.
Proof.
  split.
  - induction files as [|[p ds] rest IH]; cbn; [discriminate|].
    destruct (String.eqb path p) eqn:E; intros H.
    + apply String.eqb_eq in E; subst; inversion H; constructor.
    + constructor; [apply String.eqb_neq; exact E|apply IH; exact H].
  - intros H; induction H; cbn.
    + rewrite String.eqb_refl; reflexivity.
    + apply String.eqb_neq in H; rewrite H; exact IHfile_entry.
Qed.
Lemma file_entry_key path files items : file_entry path files items -> In path (map fst files).
Proof. intros H; induction H; cbn; auto. Qed.

Lemma expand_items_with_sound files active walk :
  (forall seen path ds done, walk seen path = Some (ds,done) -> visits files active seen path ds done) ->
  forall items seen ds done, expand_items_with walk items seen = Some (ds,done) ->
  expands_items files active seen items ds done.
Proof.
  intros W items; induction items as [|[d|path] rest IH]; intros seen ds done H; cbn in H.
  - inversion H; constructor.
  - destruct (expand_items_with walk rest seen) as [[tail mid]|] eqn:E; [|discriminate].
    inversion H; subst; constructor; eapply IH; exact E.
  - destruct (walk seen path) as [[head mid]|] eqn:V; [|discriminate].
    destruct (expand_items_with walk rest mid) as [[tail final]|] eqn:E; [|discriminate].
    inversion H; subst; econstructor; [eapply W; exact V|eapply IH; exact E].
Qed.
Theorem visit_tp_sound fuel files active seen path ds done :
  visit_tp fuel files active seen path = Some (ds,done) -> visits files active seen path ds done.
Proof.
  revert active seen path ds done; induction fuel as [|fuel IH]; intros active seen path ds done H;
    cbn [visit_tp] in H; [discriminate|].
  destruct (contains_file path active) eqn:A; [discriminate|].
  destruct (contains_file path seen) eqn:S.
  - inversion H; subst; constructor; [apply contains_file_false; exact A|apply contains_file_correct; exact S].
  - destruct (lookup_file path files) as [items|] eqn:F; [|discriminate].
    destruct (expand_items_with _ items seen) as [[decls final]|] eqn:E; [|discriminate].
    inversion H; subst; econstructor.
    + apply contains_file_false; exact A.
    + apply contains_file_false; exact S.
    + apply lookup_file_correct; exact F.
    + eapply expand_items_with_sound; [intros; eapply IH; eassumption|exact E].
Qed.

(** The active stack has distinct keys from the finite table. Thus entering
    another new file always leaves enough depth at budget 1 + table length. *)
Theorem imports_complete files :
  (forall active seen path ds done, visits files active seen path ds done ->
    NoDup active -> incl active (map fst files) -> forall fuel,
    List.length files < fuel + List.length active ->
    visit_tp fuel files active seen path = Some (ds,done)) /\
  (forall active seen items ds done, expands_items files active seen items ds done ->
    NoDup active -> incl active (map fst files) -> forall fuel,
    List.length files < fuel + List.length active ->
    expand_tp_items fuel files active seen items = Some (ds,done)).
Proof.
  apply imports_ind.
  - intros active seen path A S ND IN fuel LE.
    assert (POS : 0 < fuel).
    { pose proof (NoDup_incl_length ND IN) as B; rewrite length_map in B; lia. }
    destruct fuel; [lia|]; cbn [visit_tp].
    rewrite (proj2 (contains_file_false _ _) A), (proj2 (contains_file_correct _ _) S); reflexivity.
  - intros active seen path items ds done A S F E IH ND IN fuel LE.
    assert (POS : 0 < fuel).
    { pose proof (NoDup_incl_length ND IN) as B; rewrite length_map in B; lia. }
    destruct fuel; [lia|]; cbn [visit_tp].
    rewrite (proj2 (contains_file_false _ _) A), (proj2 (contains_file_false _ _) S).
    rewrite (proj2 (lookup_file_correct _ _ _) F).
    change (match expand_tp_items fuel files (path::active) seen items with
      | Some (ds,done) => Some (ds,path::done) | None => None end = Some (ds,path::done)).
    rewrite IH; [reflexivity|constructor; assumption|..].
    + intros p [EQ|I]; [subst; eapply file_entry_key; exact F|apply IN; exact I].
    + cbn; lia.
  - intros; reflexivity.
  - intros active seen d rest ds done E IH ND IN fuel LE.
    unfold expand_tp_items in *; cbn; rewrite IH; auto.
  - intros active seen path rest ds mid tail done V IV E IE ND IN fuel LE.
    unfold expand_tp_items in *; cbn; rewrite IV, IE; auto.

Qed.
Theorem load_tp_correct files entry ds : load_tp files entry = Some ds <-> imports_program files entry ds.
Proof.
  unfold load_tp, imports_program; split.
  - destruct (visit_tp (import_budget files) files [] [] entry) as [[decls done]|] eqn:E;
      intros H; inversion H; subst.
    exists done; eapply visit_tp_sound; exact E.
  - intros [done V]; rewrite (proj1 (imports_complete files) _ _ _ _ _ V);
      [reflexivity|constructor|intros p I; inversion I|unfold import_budget; cbn; lia].
Qed.
