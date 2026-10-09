From Stdlib Require Import List String Ascii Arith Lia DecimalString DecimalNat.
Import ListNotations.
Open Scope string_scope.
From Tinyprover.Proofglyph Require Export CodecCorrectness.

Lemma scan_digits_stop s : stops_number s -> scan_digits s = (Decimal.Nil, s).
Proof. destruct s; cbn; auto; intros H; rewrite H; reflexivity. Qed.

Lemma scan_digits_prefix u suffix : stops_number suffix ->
  scan_digits (NilEmpty.string_of_uint u ++ suffix) = (u, suffix).
Proof.
  intros H; induction u; cbn [NilEmpty.string_of_uint String.append scan_digits digit];
    try rewrite IHu; try reflexivity; apply scan_digits_stop; exact H.
Qed.

Lemma to_uint_nonempty n : Nat.to_uint n <> Decimal.Nil.
Proof.
  intros H; pose proof (Unsigned.of_to n) as E; rewrite H in E.
  cbn in E; subst n; discriminate.
Qed.

Lemma read_number_encoded n suffix : stops_number suffix ->
  read_number (NilEmpty.string_of_uint (Nat.to_uint n) ++ suffix) = Some (n, suffix).
Proof.
  intros H; unfold read_number; rewrite scan_digits_prefix by exact H.
  pose proof (to_uint_nonempty n) as NE.
  pose proof (Unsigned.of_to n) as E.
  destruct (Nat.to_uint n); try contradiction; rewrite E; reflexivity.
Qed.

Lemma instructions_stop code : stops_number (instructions_bytes code).
Proof. destruct code as [|i rest]; [exact I|]; destruct i; reflexivity. Qed.

Lemma lex_instruction i code fuel :
  lex_proofglyph (S fuel) (instruction_bytes i ++ instructions_bytes code) =
  option_map (cons i) (lex_proofglyph fuel (instructions_bytes code)).
Proof.
  destruct i; cbn [instruction_bytes String.append lex_proofglyph]; try reflexivity;
    rewrite read_number_encoded by apply instructions_stop; reflexivity.
Qed.

Theorem lex_instructions_roundtrip code fuel : List.length code <= fuel ->
  lex_proofglyph fuel (instructions_bytes code) = Some code.
Proof.
  revert fuel; induction code as [|i code IH]; intros fuel H; [destruct fuel; reflexivity|].
  destruct fuel; [cbn in H; lia|].
  change (lex_proofglyph (S fuel) (instruction_bytes i ++ instructions_bytes code) = Some (i :: code)).
  rewrite lex_instruction, IH by (cbn in H; lia); reflexivity.
Qed.

Lemma byte_length_append a b : String.length (a ++ b) = String.length a + String.length b.
Proof. induction a; cbn; [reflexivity|rewrite IHa; reflexivity]. Qed.

Lemma instructions_byte_length code : List.length code <= String.length (instructions_bytes code).
Proof.
  induction code as [|i code IH]; [reflexivity|].
  cbn [instructions_bytes List.length]; rewrite byte_length_append.
  assert (H : 1 <= String.length (instruction_bytes i)) by (destruct i; cbn; lia).
  lia.
Qed.

Lemma execute_app a b s : execute (a ++ b) s =
  match execute a s with Some s' => execute b s' | None => None end.
Proof.
  revert s; induction a as [|i a IH]; intros s; cbn; [reflexivity|].
  destruct (step i s); [apply IH|reflexivity].
Qed.

Theorem term_code_correct t stack ds : execute (term_code t) (stack, ds) = Some (t :: stack, ds).
Proof.
  revert stack ds; induction t; intros stack ds; cbn [term_code]; try reflexivity;
    rewrite execute_app, IHt1; cbn; rewrite execute_app, IHt2; reflexivity.
Qed.

Lemma declaration_code_correct d ds : execute (declaration_code d) ([], ds) = Some ([], d :: ds).
Proof.
  destruct d; cbn [declaration_code]; rewrite execute_app, term_code_correct; cbn;
    try reflexivity; rewrite execute_app, term_code_correct; reflexivity.
Qed.

Theorem program_code_correct ds acc : execute (program_code ds) ([], acc) = Some ([], rev ds ++ acc)%list.
Proof.
  revert acc; induction ds as [|d ds IH]; intros acc; cbn [program_code]; [reflexivity|].
  rewrite execute_app, declaration_code_correct; cbn; rewrite IH.
  cbn [rev]; rewrite <- app_assoc; reflexivity.
Qed.

Theorem proofglyph_roundtrip ds : decode_proofglyph (encode_proofglyph ds) = Some ds.
Proof.
  unfold decode_proofglyph, encode_proofglyph.
  rewrite lex_instructions_roundtrip by apply instructions_byte_length.
  unfold decode_instructions; rewrite program_code_correct, app_nil_r, rev_involutive; reflexivity.
Qed.

Corollary encode_proofglyph_injective ds es : encode_proofglyph ds = encode_proofglyph es -> ds = es.
Proof.
  intros H; apply (f_equal decode_proofglyph) in H; rewrite !proofglyph_roundtrip in H; congruence.
Qed.

Corollary proofglyph_canonical_roundtrip bytes ds : decode_proofglyph bytes = Some ds ->
  decode_proofglyph (encode_proofglyph ds) = decode_proofglyph bytes.
Proof. intros H; rewrite H; apply proofglyph_roundtrip. Qed.
