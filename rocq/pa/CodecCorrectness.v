From Stdlib Require Import List String Ascii Arith Lia DecimalNat.
From Tinyprover.Pa Require Export CodecImpl.
Import ListNotations.
Open Scope string_scope.

Lemma decimal_run_correct s u suffix :
  scan_digits s = (u,suffix) <-> decimal_run s u suffix.
Proof.
  split.
  - revert u suffix; induction s as [|c rest IH]; intros u suffix H; cbn in H.
    + inversion H; constructor; exact I.
    + destruct (digit c) eqn:D.
      * destruct (scan_digits rest) as [v tail] eqn:R; inversion H; subst.
        econstructor; [exact D|apply IH; reflexivity].
      * inversion H; subst; constructor; exact D.
  - intros H; induction H.
    + destruct s; cbn in *; [reflexivity|rewrite H; reflexivity].
    + cbn; rewrite H, IHdecimal_run; reflexivity.
Qed.
Lemma read_number_correct s n suffix :
  read_number s = Some (n,suffix) <-> decimal_number s n suffix.
Proof.
  unfold read_number, decimal_number; destruct (scan_digits s) as [u tail] eqn:E.
  split.
  - destruct u; intros H; inversion H; subst; eexists; repeat split;
      try discriminate; apply decimal_run_correct; exact E.
  - intros [v [NE [R N]]]; apply decimal_run_correct in R.
    rewrite E in R; inversion R; subst v tail; subst n; destruct u; [contradiction|..]; reflexivity.
Qed.
Lemma decimal_run_length s u suffix : decimal_run s u suffix ->
  String.length suffix <= String.length s.
Proof. intros H; induction H; cbn; lia. Qed.
Lemma number_suffix_length s n suffix : decimal_number s n suffix ->
  String.length suffix <= String.length s.
Proof. intros [u [_ [H _]]]; eapply decimal_run_length; exact H. Qed.

Lemma fixed_byte_other c i : fixed_byte c = Some i ->
  Ascii.eqb c "$"%char = false /\ Ascii.eqb c "#"%char = false /\ pa_space c = false.
Proof.
  destruct c as [a b c d e f g h];
    destruct a,b,c,d,e,f,g,h; cbn; intros H; try discriminate; auto.
Qed.
Lemma space_other c : pa_space c = true ->
  fixed_byte c = None /\ Ascii.eqb c "$"%char = false /\ Ascii.eqb c "#"%char = false.
Proof.
  destruct c as [a b c d e f g h];
    destruct a,b,c,d,e,f,g,h; cbn; intros H; try discriminate; auto.
Qed.

Theorem lex_pa_sound fuel bytes code :
  lex_pa fuel bytes = Some code -> pa_lexes bytes code.
Proof.
  revert bytes code; induction fuel as [|fuel IH]; intros [|c rest] code H;
    cbn [lex_pa] in H.
  - inversion H; constructor.
  - discriminate.
  - inversion H; constructor.
  - destruct (fixed_byte c) as [i|] eqn:F.
    + destruct (lex_pa fuel rest) eqn:L; inversion H; subst.
      eapply pa_lex_fixed; [exact F|apply IH; exact L].
    + destruct (Ascii.eqb c "$"%char) eqn:V.
      * apply Ascii.eqb_eq in V; subst c.
        destruct (read_number rest) as [[n suffix]|] eqn:N; [|discriminate].
        destruct (lex_pa fuel suffix) eqn:L; inversion H; subst.
        eapply pa_lex_var; [apply read_number_correct; exact N|apply IH; exact L].
      * destruct (Ascii.eqb c "#"%char) eqn:C.
        -- apply Ascii.eqb_eq in C; subst c.
           destruct (read_number rest) as [[n suffix]|] eqn:N; [|discriminate].
           destruct (lex_pa fuel suffix) eqn:L; inversion H; subst.
           eapply pa_lex_const; [apply read_number_correct; exact N|apply IH; exact L].
        -- destruct (pa_space c) eqn:S; [|discriminate].
           eapply pa_lex_space; [exact S|apply IH; exact H].
Qed.

Theorem lex_pa_complete bytes code : pa_lexes bytes code ->
  forall fuel, String.length bytes <= fuel -> lex_pa fuel bytes = Some code.
Proof.
  intros H; induction H; intros fuel LE.
  { destruct fuel; reflexivity. }
  all: destruct fuel as [|fuel]; [cbn in LE; lia|]; cbn [lex_pa].
  - destruct (space_other _ H) as [F [V C]]; rewrite F,V,C,H.
    apply IHpa_lexes; cbn in LE; lia.
  - rewrite H, IHpa_lexes by (cbn in LE; lia); reflexivity.
  - cbn [fixed_byte Ascii.eqb]; rewrite (proj2 (read_number_correct _ _ _) H).
    rewrite IHpa_lexes; [reflexivity|].
    pose proof (number_suffix_length _ _ _ H); cbn in LE; lia.
  - cbn [fixed_byte Ascii.eqb]; rewrite (proj2 (read_number_correct _ _ _) H).
    rewrite IHpa_lexes; [reflexivity|].
    pose proof (number_suffix_length _ _ _ H); cbn in LE; lia.
Qed.
Theorem lex_pa_correct bytes code :
  lex_pa (String.length bytes) bytes = Some code <-> pa_lexes bytes code.
Proof. split; [apply lex_pa_sound|intros H; apply lex_pa_complete; auto]. Qed.

Lemma step_correct i s final : step i s = Some final <-> instruction_step i s final.
Proof.
  split.
  - destruct s as [stack ds]; destruct i; cbn [step];
      repeat match goal with |- context [match ?s with [] => _ | _ => _ end] => destruct s end;
      intros H; inversion H; subst; constructor.
  - intros H; destruct H; reflexivity.
Qed.
Lemma execute_correct code s final : execute code s = Some final <->
  instructions_execute code s final.
Proof.
  split.
  - revert s; induction code as [|i code IH]; intros s H; cbn in H.
    + inversion H; constructor.
    + destruct (step i s) eqn:E; [|discriminate].
      econstructor; [apply step_correct; exact E|apply IH; exact H].
  - intros H; induction H; cbn; [reflexivity|].
    rewrite (proj2 (step_correct _ _ _) H); exact IHinstructions_execute.
Qed.
Theorem decode_pa_correct bytes ds : decode_pa bytes = Some ds <-> pa_decodes bytes ds.
Proof.
  unfold decode_pa, decode_instructions, pa_decodes; split.
  - destruct (lex_pa (String.length bytes) bytes) as [code|] eqn:L; [|discriminate].
    destruct (execute code ([],[])) as [[stack acc]|] eqn:E; [|discriminate].
    destruct stack; [|discriminate]; intros H; inversion H; subst.
    exists code; split; [eapply lex_pa_sound; exact L|].
    rewrite rev_involutive; apply execute_correct; exact E.
  - intros [code [L E]]; apply lex_pa_correct in L; apply execute_correct in E.
    rewrite L,E,rev_involutive; reflexivity.
Qed.
