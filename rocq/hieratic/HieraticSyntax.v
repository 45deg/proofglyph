From Stdlib Require Import List String Ascii Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
From Proofglyph.Hieratic Require Export HieraticSyntaxImpl.

Lemma consume_correct word ts tail : consume word ts = Some tail <-> token_at word ts tail.
Proof.
  destruct ts as [|[s|p] rest]; cbn [consume]; unfold token_at; split; intros H;
    try discriminate; try (inversion H; subst; rewrite String.eqb_refl; reflexivity).
  - destruct (String.eqb word s) eqn:E; [|discriminate].
    apply String.eqb_eq in E; inversion H; subst; reflexivity.
Qed.
Lemma consume_none word ts : consume word ts = None <-> not_at word ts.
Proof.
  unfold not_at; split.
  - intros H tail T; apply consume_correct in T; congruence.
  - destruct (consume word ts) eqn:E; [|auto].
    intros H; exfalso; apply (H l); apply consume_correct; exact E.
Qed.
Lemma parameter_names_correct ts ns tail : parameter_names ts = (ns,tail) <-> names_prefix ts ns tail.
Proof.
  split.
  - revert ns tail; induction ts as [|[n|p] rest IH]; intros ns tail H; cbn [parameter_names] in H.
    + inversion H; subst; constructor; intros; discriminate.
    + destruct (name_token (Word n)) eqn:N.
      * destruct (parameter_names rest) as [names final] eqn:E; inversion H; subst.
        constructor; [exact N|apply IH; reflexivity].
      * inversion H; subst; constructor; intros x rest' E; inversion E; subst; exact N.
    + inversion H; subst; constructor; intros; discriminate.
  - intros H; induction H.
    + destruct ts as [|[n|p] rest]; cbn [parameter_names]; try reflexivity.
      rewrite (H n rest eq_refl); reflexivity.
    + cbn [parameter_names]; rewrite H, IHnames_prefix; reflexivity.
Qed.
Lemma names_prefix_length ts ns tail : names_prefix ts ns tail ->
  List.length ts = List.length ns + List.length tail.
Proof. intros H; induction H; cbn; lia. Qed.
Lemma atom_starts ts e tail : atom_parses ts e tail ->
  exists t rest, ts = t::rest /\ starts_atom t = true.
Proof.
  intros H; destruct H.
  - exists (Word "Type"), tail; split; reflexivity.
  - exists (Word "Kind"), tail; split; reflexivity.
  - exists (Word n), tail; split; [reflexivity|].
    cbn [starts_atom]; rewrite H, !orb_true_r; reflexivity.
  - exists (Word "("), ts; split; reflexivity.
Qed.

Ltac syntax_cases H :=
  repeat match type of H with
  | context [option_map ?f ?v] => let E := fresh "mapped" in destruct v eqn:E; cbn [option_map] in H
  | context [if ?b then _ else _] => let E := fresh "branch" in destruct b eqn:E
  | context [match ?v with _ => _ end] => let E := fresh "value" in destruct v eqn:E
  end; try discriminate.

Lemma token_here word tail : token_at word (Word word::tail) tail.
Proof. reflexivity. Qed.
Lemma forall_parses ts ps after body b final :
  parameters_parse ts ps after -> ps <> PNil -> token_at "," after body ->
  term_parses body b final -> term_parses (Word "forall"::ts) (RForall ps b) final.
Proof. intros; eapply (term_binder "forall"); eauto; reflexivity. Qed.
Lemma lambda_parses ts ps after body b final :
  parameters_parse ts ps after -> ps <> PNil -> token_at "=>" after body ->
  term_parses body b final -> term_parses (Word "fun"::ts) (RLambda ps b) final.
Proof. intros; eapply (term_binder "fun"); eauto; reflexivity. Qed.
Lemma group_nonempty x xs a ps : PGroup x xs a ps <> PNil.
Proof. discriminate. Qed.
Ltac syntax_equations :=
  repeat match goal with
  | E : consume _ _ = Some _ |- _ => apply consume_correct in E; unfold token_at in E; subst
  | E : String.eqb _ _ = true |- _ => apply String.eqb_eq in E; subst
  | E : true || _ = true |- _ => clear E
  | E : false || _ = true |- _ => cbn in E
  end.

Lemma consume_sound word ts tail : consume word ts = Some tail -> token_at word ts tail.
Proof. apply consume_correct. Qed.
Lemma consume_absent word ts : consume word ts = None -> not_at word ts.
Proof. apply consume_none. Qed.
Lemma names_prefix_sound ts ns tail : parameter_names ts = (ns,tail) -> names_prefix ts ns tail.
Proof. apply parameter_names_correct. Qed.

Theorem parsers_sound fuel :
  (forall ts e tail, parse_term fuel ts = Some (e,tail) -> term_parses ts e tail) /\
  (forall ts e tail, parse_atom fuel ts = Some (e,tail) -> atom_parses ts e tail) /\
  (forall a ts e tail, parse_application fuel a ts = Some (e,tail) -> application_parses a ts e tail) /\
  (forall ts ps tail, parse_parameters fuel ts = Some (ps,tail) -> parameters_parse ts ps tail).
Proof.
  induction fuel as [|fuel [TERM [ATOM [APP PARAM]]]].
  { repeat split; intros; discriminate. }
  repeat split.
  - intros ts e tail H; cbn [parse_term] in H; syntax_cases H;
      inversion H; subst; syntax_equations; eauto 12 using forall_parses, lambda_parses, group_nonempty, token_here, term_plain, term_arrow,
      consume_sound, consume_absent.
  - intros ts e tail H; cbn [parse_atom] in H; syntax_cases H;
      inversion H; subst; syntax_equations; eauto 10 using token_here, atom_type, atom_kind, atom_name, atom_parens,
      consume_sound.
  - intros a ts e tail H; cbn [parse_application] in H; syntax_cases H;
      inversion H; subst; eauto 10 using application_more.
    all: apply application_end; intros tok rest E; inversion E; subst; assumption.
  - intros ts ps tail H; cbn [parse_parameters] in H; syntax_cases H;
      inversion H; subst; syntax_equations; eauto 12 using token_here, parameters_end, parameters_group,
      consume_sound, consume_absent,
      names_prefix_sound.
Qed.

Lemma name_keywords n : name_token (Word n) = true ->
  String.eqb n "Type" = false /\ String.eqb n "Kind" = false /\
  String.eqb n "forall" = false /\ String.eqb n "fun" = false.
Proof.
  destruct n as [|c rest]; [discriminate|].
  cbn [name_token]; intros H; apply andb_true_iff in H as [_ R].
  apply negb_true_iff in R; cbn [reserved existsb] in R.
  repeat rewrite orb_false_iff in R; tauto.
Qed.
Lemma name_not_paren n : name_token (Word n) = true -> String.eqb n "(" = false.
Proof.
  intros H; destruct (String.eqb n "(") eqn:E; [|reflexivity].
  apply String.eqb_eq in E; subst; discriminate.
Qed.
Lemma atom_term_prefix ts e tail : atom_parses ts e tail ->
  exists w rest, ts = Word w::rest /\ (String.eqb w "forall" || String.eqb w "fun") = false.
Proof.
  intros H; destruct H; eexists; eexists; split; [reflexivity|..]; try reflexivity.
  destruct (name_keywords _ H) as [_ [_ [F G]]]; rewrite F,G; reflexivity.
Qed.

Theorem syntax_complete :
  (forall ts e tail, term_parses ts e tail ->
    List.length tail < List.length ts /\ forall fuel,
      4 * (List.length ts - List.length tail) + 1 <= fuel -> parse_term fuel ts = Some (e,tail)) /\
  (forall ts e tail, atom_parses ts e tail ->
    List.length tail < List.length ts /\ forall fuel,
      4 * (List.length ts - List.length tail) <= fuel -> parse_atom fuel ts = Some (e,tail)) /\
  (forall a ts e tail, application_parses a ts e tail ->
    List.length tail <= List.length ts /\ forall fuel,
      4 * (List.length ts - List.length tail) + 1 <= fuel -> parse_application fuel a ts = Some (e,tail)) /\
  (forall ts ps tail, parameters_parse ts ps tail ->
    List.length tail <= List.length ts /\ forall fuel,
      4 * (List.length ts - List.length tail) + 1 <= fuel -> parse_parameters fuel ts = Some (ps,tail)).
Proof.
  apply syntax_ind.
  - intros w ts ps after body b final K P [PL PC] NE AT T [TL TC].
    unfold token_at in AT; subst after; cbn [List.length] in PL.
    split; [cbn [List.length]; lia|]. intros fuel LE; destruct fuel as [|fuel]; [lia|].
    cbn [parse_term]; rewrite K, PC by (cbn [List.length] in *; lia).
    destruct ps; [contradiction|].
    rewrite (proj2 (consume_correct _ _ _) eq_refl), TC by (cbn [List.length] in *; lia); reflexivity.
  - intros ts a after out tail A [AL AC] APP [PL PC] STOP.
    split; [lia|]. intros fuel LE; destruct fuel as [|fuel]; [lia|].
    destruct (atom_term_prefix _ _ _ A) as [w [rest [E K]]]; subst ts.
    cbn [parse_term]; rewrite K, AC, PC by (cbn [List.length] in *; lia).
    rewrite (proj2 (consume_none _ _) STOP); reflexivity.
  - intros ts a after left tail right final A [AL AC] APP [PL PC] T [TL TC].
    cbn [List.length] in PL; split; [lia|]. intros fuel LE; destruct fuel as [|fuel]; [lia|].
    destruct (atom_term_prefix _ _ _ A) as [w [rest [E K]]]; subst ts.
    cbn [parse_term]; rewrite K, AC, PC by (cbn [List.length] in *; lia).
    cbn [consume]; rewrite String.eqb_refl, TC by (cbn [List.length] in *; lia); reflexivity.
  - intros tail; split; [cbn [List.length]; lia|]. intros fuel LE; destruct fuel; [cbn [List.length] in *; lia|reflexivity].
  - intros tail; split; [cbn [List.length]; lia|]. intros fuel LE; destruct fuel; [cbn [List.length] in *; lia|reflexivity].
  - intros n tail N; split; [cbn [List.length]; lia|]. intros fuel LE; destruct fuel; [cbn [List.length] in *; lia|].
    cbn [parse_atom]; destruct (name_keywords _ N) as [TY [KI _]].
    rewrite TY,KI,(name_not_paren _ N),N; reflexivity.
  - intros ts e tail T [TL TC]; cbn [List.length] in TL.
    split; [cbn [List.length]; lia|]. intros fuel LE; destruct fuel as [|fuel]; [cbn [List.length] in *; lia|].
    cbn [parse_atom]; rewrite TC by (cbn [List.length] in *; lia); reflexivity.
  - intros a ts STOP; split; [lia|]. intros fuel LE; destruct fuel; [lia|].
    cbn [parse_application]; destruct ts as [|t rest]; [reflexivity|].
    rewrite (STOP t rest eq_refl); reflexivity.
  - intros a ts b after out final A [AL AC] APP [PL PC].
    split; [lia|]. intros fuel LE; destruct fuel as [|fuel]; [lia|].
    destruct (atom_starts _ _ _ A) as [t [rest [E START]]]; subst ts.
    cbn [parse_application]; rewrite START, AC, PC by (cbn [List.length] in *; lia); reflexivity.
  - intros ts STOP; split; [lia|]. intros fuel LE; destruct fuel; [lia|].
    cbn [parse_parameters]; rewrite (proj2 (consume_none _ _) STOP); reflexivity.
  - intros ts n ns after_names a after_type ps tail N T [TL TC] P [PL PC].
    pose proof (names_prefix_length _ _ _ N) as NL; cbn [List.length] in NL,TL.
    split; [cbn [List.length]; lia|]. intros fuel LE; destruct fuel as [|fuel]; [cbn [List.length] in *; lia|].
    cbn [parse_parameters]; rewrite (proj2 (consume_correct "(" _ _) eq_refl).
    rewrite (proj2 (parameter_names_correct _ _ _) N).
    rewrite (proj2 (consume_correct ":" _ _) eq_refl); rewrite TC by (cbn [List.length] in *; lia).
    rewrite (proj2 (consume_correct ")" _ _) eq_refl); rewrite PC by (cbn [List.length] in *; lia); reflexivity.
Qed.

Lemma term_parser_sound fuel ts e tail : parse_term fuel ts = Some (e,tail) -> term_parses ts e tail.
Proof. apply (proj1 (parsers_sound fuel)). Qed.
Lemma parameters_parser_sound fuel ts ps tail : parse_parameters fuel ts = Some (ps,tail) -> parameters_parse ts ps tail.
Proof. apply (proj2 (proj2 (proj2 (parsers_sound fuel)))). Qed.
Lemma declaration_not_import kind : declaration_keyword kind = true -> kind <> "import".
Proof. intros H E; subst; discriminate. Qed.
Theorem items_parser_sound fuel ts items : parse_items_hieratic fuel ts = Some items -> items_parse ts items.
Proof.
  revert ts items; induction fuel as [|fuel IH]; intros ts items H; [discriminate|].
  cbn [parse_items_hieratic] in H; syntax_cases H; inversion H; subst; syntax_equations.
  all: repeat match goal with E : context [match _ with _ => _ end] |- _ =>
    syntax_cases E; inversion E; clear E; subst; syntax_equations end.
  all: repeat match goal with
    | E : _ && _ = true |- _ => apply andb_true_iff in E as [? ?]
    | E : String.eqb _ _ = false |- _ => apply String.eqb_neq in E
    end.
  all: first [apply items_parse_nil | apply items_parse_import | eapply items_parse_decl].
  all: eauto 3 using body_axiom, body_proof,
    parameters_parser_sound, term_parser_sound, consume_sound, token_here.
Qed.

Lemma body_parse_length kind ps ts body tail : body_parses kind ps ts body tail ->
  List.length tail <= List.length ts.
Proof.
  intros H; destruct H; [lia|].
  pose proof (proj1 (proj1 syntax_complete _ _ _ H0)); cbn [List.length]; lia.
Qed.
Theorem items_parser_complete ts items : items_parse ts items -> forall fuel,
  4 * List.length ts + 1 <= fuel -> parse_items_hieratic fuel ts = Some items.
Proof.
  intros H; induction H.
  - intros [|fuel] LE; [lia|reflexivity].
  - intros [|fuel] LE; [lia|]. cbn [parse_items_hieratic].
    apply String.eqb_neq in H; rewrite String.eqb_refl,H.
    rewrite (proj2 (consume_correct ";" _ _) eq_refl), IHitems_parse by (cbn [List.length] in *; lia); reflexivity.
  - intros [|fuel] LE; [lia|].
    pose proof (proj2 (proj2 (proj2 syntax_complete)) _ _ _ H1) as [PL PC].
    unfold token_at in H2; subst after_ps; cbn [List.length] in PL.
    pose proof (proj1 syntax_complete _ _ _ H3) as [TL TC].
    pose proof (body_parse_length _ _ _ _ _ H4) as BL; cbn [List.length] in BL.
    cbn [parse_items_hieratic]; rewrite (proj2 (String.eqb_neq _ _) (declaration_not_import _ H)).
    rewrite H,H0; cbn [andb]. rewrite PC by (cbn [List.length] in *; lia).
    rewrite (proj2 (consume_correct ":" _ _) eq_refl), TC by (cbn [List.length] in *; lia).
    inversion H4; subst.
    + match goal with E : assumption_keyword kind = true |- _ => rewrite E end.
      rewrite (proj2 (consume_correct ";" _ _) eq_refl), IHitems_parse by (cbn [List.length] in *; lia); reflexivity.
    + match goal with E : assumption_keyword kind = false |- _ => rewrite E end.
      rewrite (proj2 (consume_correct ":=" _ _) eq_refl).
      match goal with B : term_parses _ _ (Word ";"::rest) |- _ =>
        pose proof (proj1 syntax_complete _ _ _ B) as BTBC end.
      destruct BTBC as [BT BC].
      rewrite BC by (cbn [List.length] in *; lia).
      rewrite (proj2 (consume_correct ";" _ _) eq_refl), IHitems_parse by (cbn [List.length] in *; lia); reflexivity.
Qed.

Lemma span_correct p s prefix suffix : span p s = (prefix,suffix) <-> maximal_span p s prefix suffix.
Proof.
  split.
  - revert prefix suffix; induction s as [|c rest IH]; intros prefix suffix H; cbn [span] in H.
    + inversion H; constructor.
    + destruct (p c) eqn:E.
      * destruct (span p rest) as [a b] eqn:R; inversion H; subst.
        constructor; [exact E|apply IH; reflexivity].
      * inversion H; subst; constructor; exact E.
  - intros H; induction H; cbn [span]; try rewrite H; try rewrite IHmaximal_span; reflexivity.
Qed.
Lemma span_length p s prefix suffix : maximal_span p s prefix suffix -> String.length suffix <= String.length s.
Proof. intros H; induction H; cbn [String.length]; lia. Qed.
Lemma quoted_correct s path suffix : quoted s = Some (path,suffix) <-> quoted_path s path suffix.
Proof.
  split.
  - revert path suffix; induction s as [|c rest IH]; intros path suffix H; [discriminate|].
    cbn [quoted] in H; destruct (Ascii.eqb c """"%char) eqn:Q.
    + apply Ascii.eqb_eq in Q; subst c; inversion H; constructor.
    + destruct (path_forbidden c) eqn:F.
      * unfold path_forbidden in F; rewrite F in H; discriminate.
      * unfold path_forbidden in F; rewrite F in H.
        destruct (quoted rest) as [[a b]|] eqn:E; [|discriminate].
        inversion H; subst; constructor; [exact Q|exact F|apply IH; reflexivity].
  - intros H; induction H; cbn [quoted].
    + reflexivity.
    + rewrite H; unfold path_forbidden in H0; rewrite H0, IHquoted_path; reflexivity.
Qed.
Lemma quoted_length s path suffix : quoted_path s path suffix -> String.length suffix < String.length s.
Proof. intros H; induction H; cbn [String.length]; lia. Qed.

Theorem chunk_correct bytes token suffix : next_chunk bytes = Some (token,suffix) <-> lexical_step bytes token suffix.
Proof.
  split.
  - destruct bytes as [|c rest]; [discriminate|].
    cbn [next_chunk]; destruct (byte_class c) eqn:C.
    + intros H; inversion H; subst; constructor; exact C.
    + destruct rest as [|d tail]; [discriminate|].
      destruct (Ascii.eqb d "/"%char) eqn:D; [|discriminate].
      apply Ascii.eqb_eq in D; subst d.
      destruct (span _ tail) as [prefix final] eqn:E; cbn; intros H; inversion H; subst.
      eapply lex_comment; [exact C|apply span_correct; exact E].
    + destruct (span ident rest) as [prefix final] eqn:E; intros H; inversion H; subst.
      eapply lex_word; [exact C|apply span_correct; exact E].
    + destruct (quoted rest) as [[path final]|] eqn:E; [|discriminate].
      intros H; inversion H; subst; eapply lex_path; [exact C|apply quoted_correct; exact E].
    + destruct rest as [|d tail].
      * destruct (Ascii.eqb c ":"%char) eqn:D; intros H; inversion H; subst.
        apply lex_colon; auto; exact I.
      * destruct (pair_symbol c d) eqn:P.
        -- intros H; inversion H; subst; constructor; assumption.
        -- destruct (Ascii.eqb c ":"%char) eqn:D; intros H; inversion H; subst.
           apply lex_colon; auto.
    + intros H; inversion H; subst; constructor; exact C.
    + discriminate.
  - intros H; destruct H; cbn [next_chunk]; rewrite H; try reflexivity.
    + destruct (span _ rest) as [a b] eqn:E.
      apply span_correct in H0; rewrite H0 in E; inversion E; reflexivity.
    + apply span_correct in H0; rewrite H0; reflexivity.
    + apply quoted_correct in H0; rewrite H0; reflexivity.
    + rewrite H0; reflexivity.
    + destruct rest; cbn in H1; [rewrite H0|rewrite H1,H0]; reflexivity.
Qed.
Lemma chunk_progress bytes token suffix : lexical_step bytes token suffix ->
  String.length suffix < String.length bytes.
Proof.
  intros H; destruct H; cbn [String.length]; try lia.
  - pose proof (span_length _ _ _ _ H0); lia.
  - pose proof (span_length _ _ _ _ H0); lia.
  - pose proof (quoted_length _ _ _ H0); lia.
Qed.
Theorem lex_hieratic_sound fuel bytes ts : lex_hieratic_fuel fuel bytes = Some ts -> hieratic_lexes bytes ts.
Proof.
  revert bytes ts; induction fuel as [|fuel IH]; intros bytes ts H; [discriminate|].
  destruct bytes as [|c rest]; cbn [lex_hieratic_fuel] in H.
  - inversion H; constructor.
  - destruct (next_chunk (String c rest)) as [[[token|] suffix]|] eqn:E; [| |discriminate].
    + destruct (lex_hieratic_fuel fuel suffix) eqn:L; inversion H; subst.
      econstructor; [apply chunk_correct; exact E|apply IH; exact L].
    + econstructor; [apply chunk_correct; exact E|apply IH; exact H].
Qed.
Theorem lex_hieratic_complete bytes ts : hieratic_lexes bytes ts -> forall fuel,
  String.length bytes < fuel -> lex_hieratic_fuel fuel bytes = Some ts.
Proof.
  intros H; induction H; intros fuel LE.
  { destruct fuel; [lia|reflexivity]. }
  all: destruct fuel as [|fuel]; [lia|].
  - destruct bytes; [inversion H|]; cbn [lex_hieratic_fuel].
    rewrite (proj2 (chunk_correct _ _ _) H), IHhieratic_lexes; [reflexivity|].
    pose proof (chunk_progress _ _ _ H); cbn [String.length] in *; lia.
  - destruct bytes; [inversion H|]; cbn [lex_hieratic_fuel].
    rewrite (proj2 (chunk_correct _ _ _) H), IHhieratic_lexes; [reflexivity|].
    pose proof (chunk_progress _ _ _ H); cbn [String.length] in *; lia.
Qed.
Theorem lex_hieratic_correct bytes ts : lex_hieratic bytes = Some ts <-> hieratic_lexes bytes ts.
Proof. split; [apply lex_hieratic_sound|intros H; apply lex_hieratic_complete; [exact H|lia]]. Qed.
Theorem parse_hieratic_correct bytes items : parse_hieratic bytes = Some items <-> hieratic_parses bytes items.
Proof.
  unfold parse_hieratic, hieratic_parses; split.
  - destruct (lex_hieratic bytes) as [ts|] eqn:L; [|discriminate].
    intros P; exists ts; split; [apply lex_hieratic_correct; exact L|eapply items_parser_sound; exact P].
  - intros [ts [L P]]; apply lex_hieratic_correct in L; rewrite L.
    apply items_parser_complete; [exact P|lia].
Qed.
Theorem parse_hieratic_unique bytes a b : hieratic_parses bytes a -> hieratic_parses bytes b -> a = b.
Proof. intros A B; apply parse_hieratic_correct in A; apply parse_hieratic_correct in B; congruence. Qed.
