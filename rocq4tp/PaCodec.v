From Stdlib Require Import List String Ascii Arith Lia DecimalString DecimalNat.
From Rocq4pa Require Import Syntax Program.
Import ListNotations.
Open Scope string_scope.

(** Byte syntax is separate from typing. Decoding builds raw declarations;
    callers must still use check_program before accepting a proof. *)
Inductive instruction :=
| PushType | PushKind | PushVar (n : nat) | PushConst (n : nat)
| MakePi | MakeLam | MakeApp | RegisterAssume | RegisterProve.

Definition digit (c : ascii) : option (Decimal.uint -> Decimal.uint) :=
  match c with
  | "0" => Some Decimal.D0 | "1" => Some Decimal.D1
  | "2" => Some Decimal.D2 | "3" => Some Decimal.D3
  | "4" => Some Decimal.D4 | "5" => Some Decimal.D5
  | "6" => Some Decimal.D6 | "7" => Some Decimal.D7
  | "8" => Some Decimal.D8 | "9" => Some Decimal.D9
  | _ => None
  end%char.

(** Maximal contiguous decimal run, including leading zeroes. *)
Fixpoint scan_digits (s : string) : Decimal.uint * string :=
  match s with
  | EmptyString => (Decimal.Nil, EmptyString)
  | String c rest => match digit c with
      | None => (Decimal.Nil, s)
      | Some add_digit => let '(u, suffix) := scan_digits rest in (add_digit u, suffix)
      end
  end.

Definition read_number s : option (nat * string) :=
  let '(u, suffix) := scan_digits s in
  match u with Decimal.Nil => None | _ => Some (Nat.of_uint u, suffix) end.

Definition stops_number s :=
  match s with EmptyString => True | String c _ => digit c = None end.

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

Definition instruction_bytes i : string :=
  match i with
  | PushType => "*" | PushKind => "^"
  | PushVar n => "$" ++ NilEmpty.string_of_uint (Nat.to_uint n)
  | PushConst n => "#" ++ NilEmpty.string_of_uint (Nat.to_uint n)
  | MakePi => ">" | MakeLam => "\" | MakeApp => "@"
  | RegisterAssume => ":" | RegisterProve => "!"
  end.

Fixpoint instructions_bytes code : string :=
  match code with [] => "" | i :: rest => instruction_bytes i ++ instructions_bytes rest end.

(** Fuel bounds token/whitespace steps, not typing or index magnitude.
    The public lexer supplies one step per input byte. *)
Fixpoint lex_pa fuel s : option (list instruction) :=
  match s with
  | EmptyString => Some []
  | String c rest => match fuel with
    | 0 => None
    | S fuel =>
      let next i suffix := option_map (cons i) (lex_pa fuel suffix) in
      match c with
      | "*" => next PushType rest | "^" => next PushKind rest
      | "$" => match read_number rest with
          | Some (n, suffix) => next (PushVar n) suffix | None => None end
      | "#" => match read_number rest with
          | Some (n, suffix) => next (PushConst n) suffix | None => None end
      | ">" => next MakePi rest | "\" => next MakeLam rest | "@" => next MakeApp rest
      | ":" => next RegisterAssume rest | "!" => next RegisterProve rest
      | " " | "009" | "010" | "013" => lex_pa fuel rest
      | _ => None
      end%char
    end
  end.

Lemma instructions_stop code : stops_number (instructions_bytes code).
Proof. destruct code as [|i rest]; [exact I|]; destruct i; reflexivity. Qed.

Lemma lex_instruction i code fuel :
  lex_pa (S fuel) (instruction_bytes i ++ instructions_bytes code) =
  option_map (cons i) (lex_pa fuel (instructions_bytes code)).
Proof.
  destruct i; cbn [instruction_bytes String.append lex_pa]; try reflexivity;
    rewrite read_number_encoded by apply instructions_stop; reflexivity.
Qed.

Theorem lex_instructions_roundtrip code fuel : List.length code <= fuel ->
  lex_pa fuel (instructions_bytes code) = Some code.
Proof.
  revert fuel; induction code as [|i code IH]; intros fuel H; [destruct fuel; reflexivity|].
  destruct fuel; [cbn in H; lia|].
  change (lex_pa (S fuel) (instruction_bytes i ++ instructions_bytes code) = Some (i :: code)).
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

Definition state := (list term * list declaration)%type.

Definition step (i : instruction) (s : state) : option state :=
  let '(stack, ds) := s in
  match i with
  | PushType => Some (tType :: stack, ds)
  | PushKind => Some (tKind :: stack, ds)
  | PushVar n => Some (tVar n :: stack, ds)
  | PushConst n => Some (tConst n :: stack, ds)
  | MakePi => match stack with b :: a :: rest => Some (tPi a b :: rest, ds) | _ => None end
  | MakeLam => match stack with b :: a :: rest => Some (tLam a b :: rest, ds) | _ => None end
  | MakeApp => match stack with x :: f :: rest => Some (tApp f x :: rest, ds) | _ => None end
  | RegisterAssume => match stack with [a] => Some ([], Assume a :: ds) | _ => None end
  | RegisterProve => match stack with [b; a] => Some ([], Prove a b :: ds) | _ => None end
  end.

Fixpoint execute code s : option state :=
  match code with
  | [] => Some s
  | i :: rest => match step i s with Some s' => execute rest s' | None => None end
  end.

Lemma execute_app a b s : execute (a ++ b) s =
  match execute a s with Some s' => execute b s' | None => None end.
Proof.
  revert s; induction a as [|i a IH]; intros s; cbn; [reflexivity|].
  destruct (step i s); [apply IH|reflexivity].
Qed.

Fixpoint term_code t : list instruction :=
  match t with
  | tType => [PushType] | tKind => [PushKind]
  | tVar n => [PushVar n] | tConst n => [PushConst n]
  | tPi a b => term_code a ++ term_code b ++ [MakePi]
  | tLam a b => term_code a ++ term_code b ++ [MakeLam]
  | tApp f x => term_code f ++ term_code x ++ [MakeApp]
  end%list.

Theorem term_code_correct t stack ds : execute (term_code t) (stack, ds) = Some (t :: stack, ds).
Proof.
  revert stack ds; induction t; intros stack ds; cbn [term_code]; try reflexivity;
    rewrite execute_app, IHt1; cbn; rewrite execute_app, IHt2; reflexivity.
Qed.

Definition declaration_code d :=
  match d with
  | Assume a => term_code a ++ [RegisterAssume]
  | Prove a b => term_code a ++ term_code b ++ [RegisterProve]
  end%list.

Fixpoint program_code ds :=
  match ds with [] => [] | d :: rest => declaration_code d ++ program_code rest end%list.

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

Definition decode_instructions code : option (list declaration) :=
  match execute code ([], []) with
  | Some ([], ds) => Some (rev ds)
  | _ => None
  end.

Definition encode_pa ds := instructions_bytes (program_code ds).

Definition decode_pa bytes : option (list declaration) :=
  match lex_pa (String.length bytes) bytes with
  | Some code => decode_instructions code
  | None => None
  end.

Theorem pa_roundtrip ds : decode_pa (encode_pa ds) = Some ds.
Proof.
  unfold decode_pa, encode_pa.
  rewrite lex_instructions_roundtrip by apply instructions_byte_length.
  unfold decode_instructions; rewrite program_code_correct, app_nil_r, rev_involutive; reflexivity.
Qed.

Corollary encode_pa_injective ds es : encode_pa ds = encode_pa es -> ds = es.
Proof.
  intros H; apply (f_equal decode_pa) in H; rewrite !pa_roundtrip in H; congruence.
Qed.

Corollary pa_canonical_roundtrip bytes ds : decode_pa bytes = Some ds ->
  decode_pa (encode_pa ds) = decode_pa bytes.
Proof. intros H; rewrite H; apply pa_roundtrip. Qed.
