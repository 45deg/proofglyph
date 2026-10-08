From Stdlib Require Import List String Ascii Arith Lia DecimalString DecimalNat.
Import ListNotations.
Open Scope string_scope.
From Tinyprover.Pa Require Export CodecSpec.

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
      match fixed_byte c with
      | Some i => next i rest
      | None => if Ascii.eqb c "$"%char then
          match read_number rest with Some (n,suffix) => next (PushVar n) suffix | None => None end
        else if Ascii.eqb c "#"%char then
          match read_number rest with Some (n,suffix) => next (PushConst n) suffix | None => None end
        else if pa_space c then lex_pa fuel rest else None
      end
    end
  end.

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

Fixpoint term_code t : list instruction :=
  match t with
  | tType => [PushType] | tKind => [PushKind]
  | tVar n => [PushVar n] | tConst n => [PushConst n]
  | tPi a b => term_code a ++ term_code b ++ [MakePi]
  | tLam a b => term_code a ++ term_code b ++ [MakeLam]
  | tApp f x => term_code f ++ term_code x ++ [MakeApp]
  end%list.

Definition declaration_code d :=
  match d with
  | Assume a => term_code a ++ [RegisterAssume]
  | Prove a b => term_code a ++ term_code b ++ [RegisterProve]
  end%list.

Fixpoint program_code ds :=
  match ds with [] => [] | d :: rest => declaration_code d ++ program_code rest end%list.

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

