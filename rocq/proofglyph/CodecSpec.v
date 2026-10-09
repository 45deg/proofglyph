From Stdlib Require Import List String Ascii Arith Lia DecimalString DecimalNat.
Import ListNotations.
Open Scope string_scope.
From Proofglyph.Language Require Export Syntax Program.

Inductive instruction :=
| PushType | PushKind | PushVar (n : nat) | PushConst (n : nat)
| MakePi | MakeLam | MakeApp | RegisterAssume | RegisterProve.

Definition state := (list term * list declaration)%type.

Definition digit (c : ascii) : option (Decimal.uint -> Decimal.uint) :=
  match c with
  | "0" => Some Decimal.D0 | "1" => Some Decimal.D1
  | "2" => Some Decimal.D2 | "3" => Some Decimal.D3
  | "4" => Some Decimal.D4 | "5" => Some Decimal.D5
  | "6" => Some Decimal.D6 | "7" => Some Decimal.D7
  | "8" => Some Decimal.D8 | "9" => Some Decimal.D9
  | _ => None
  end%char.

Definition stops_number s :=
  match s with EmptyString => True | String c _ => digit c = None end.


(** The lexical table and relations specify byte syntax without a lexer,
    execution function, or typing checker. *)
Definition fixed_byte (c : ascii) : option instruction :=
  match c with
  | "*" => Some PushType | "^" => Some PushKind
  | ">" => Some MakePi | "\" => Some MakeLam | "@" => Some MakeApp
  | ":" => Some RegisterAssume | "!" => Some RegisterProve
  | _ => None
  end%char.
Definition proofglyph_space (c : ascii) :=
  existsb (Ascii.eqb c) [" "%char; "009"%char; "010"%char; "013"%char].

Inductive decimal_run : string -> Decimal.uint -> string -> Prop :=
| decimal_stop : forall s, stops_number s -> decimal_run s Decimal.Nil s
| decimal_next : forall c rest add u suffix,
    digit c = Some add -> decimal_run rest u suffix ->
    decimal_run (String c rest) (add u) suffix.
Definition decimal_number s n suffix :=
  exists u, u <> Decimal.Nil /\ decimal_run s u suffix /\ n = Nat.of_uint u.

Inductive proofglyph_lexes : string -> list instruction -> Prop :=
| proofglyph_lex_nil : proofglyph_lexes "" []
| proofglyph_lex_space : forall c rest code,
    proofglyph_space c = true -> proofglyph_lexes rest code -> proofglyph_lexes (String c rest) code
| proofglyph_lex_fixed : forall c rest i code,
    fixed_byte c = Some i -> proofglyph_lexes rest code -> proofglyph_lexes (String c rest) (i::code)
| proofglyph_lex_var : forall rest n suffix code,
    decimal_number rest n suffix -> proofglyph_lexes suffix code ->
    proofglyph_lexes (String "$"%char rest) (PushVar n::code)
| proofglyph_lex_const : forall rest n suffix code,
    decimal_number rest n suffix -> proofglyph_lexes suffix code ->
    proofglyph_lexes (String "#"%char rest) (PushConst n::code).

Inductive instruction_step : instruction -> state -> state -> Prop :=
| st_type : forall s ds, instruction_step PushType (s,ds) (tType::s,ds)
| st_kind : forall s ds, instruction_step PushKind (s,ds) (tKind::s,ds)
| st_var : forall n s ds, instruction_step (PushVar n) (s,ds) (tVar n::s,ds)
| st_const : forall n s ds, instruction_step (PushConst n) (s,ds) (tConst n::s,ds)
| st_pi : forall a b s ds, instruction_step MakePi (b::a::s,ds) (tPi a b::s,ds)
| st_lam : forall a b s ds, instruction_step MakeLam (b::a::s,ds) (tLam a b::s,ds)
| st_app : forall f x s ds, instruction_step MakeApp (x::f::s,ds) (tApp f x::s,ds)
| st_assume : forall a ds, instruction_step RegisterAssume ([a],ds) ([],Assume a::ds)
| st_prove : forall a b ds, instruction_step RegisterProve ([b;a],ds) ([],Prove a b::ds).
Inductive instructions_execute : list instruction -> state -> state -> Prop :=
| exec_nil : forall s, instructions_execute [] s s
| exec_cons : forall i code s mid final,
    instruction_step i s mid -> instructions_execute code mid final ->
    instructions_execute (i::code) s final.
Definition proofglyph_decodes bytes ds :=
  exists code, proofglyph_lexes bytes code /\ instructions_execute code ([],[]) ([],rev ds).
