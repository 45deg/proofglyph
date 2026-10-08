From Stdlib Require Import List String Ascii Bool Arith.
From Rocq4tp Require Import Desugar.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

(** Byte lexer: no Unicode identifiers or escape sequences. *)
Definition letter c := let n := nat_of_ascii c in
  ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)) || (n =? 95).
Definition ident c := letter c ||
  ((48 <=? nat_of_ascii c) && (nat_of_ascii c <=? 57)) || (nat_of_ascii c =? 39).
Definition whitespace c := existsb (Ascii.eqb c) [" "%char; "009"%char; "010"%char; "013"%char].
Fixpoint span (p : ascii -> bool) (s : string) : string * string :=
  match s with
  | EmptyString => ("", "")
  | String c rest => if p c then let '(a,b) := span p rest in (String c a,b) else ("",s)
  end.
Fixpoint quoted (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c rest =>
      if Ascii.eqb c """"%char then Some ("",rest)
      else if existsb (Ascii.eqb c) ["010"%char; "013"%char; "\"%char] then None
      else match quoted rest with Some (a,b) => Some (String c a,b) | None => None end
  end.
Inductive tp_token := Word (s : string) | Path (s : string).
Fixpoint lex_tp_fuel (fuel : nat) (s : string) : option (list tp_token) :=
  match fuel with
  | 0 => None
  | S k => match s with
    | EmptyString => Some []
    | String c rest =>
      if whitespace c then lex_tp_fuel k rest else
      if Ascii.eqb c "/"%char then match rest with
        | String d tail => if Ascii.eqb d "/"%char then
            lex_tp_fuel k (snd (span (fun x => negb (Ascii.eqb x "010"%char)) tail)) else None
        | _ => None end else
      if letter c then let '(a,b) := span ident rest in
        option_map (cons (Word (String c a))) (lex_tp_fuel k b) else
      if Ascii.eqb c """"%char then match quoted rest with
        | Some (a,b) => option_map (cons (Path a)) (lex_tp_fuel k b) | None => None end else
      if existsb (Ascii.eqb c) [":"%char; "-"%char; "="%char] then
        match rest with
        | String d tail =>
          if (Ascii.eqb c ":"%char && Ascii.eqb d "="%char) ||
             ((Ascii.eqb c "-"%char || Ascii.eqb c "="%char) && Ascii.eqb d ">"%char)
          then option_map (cons (Word (String c (String d "")))) (lex_tp_fuel k tail)
          else if Ascii.eqb c ":"%char then option_map (cons (Word ":")) (lex_tp_fuel k rest) else None
        | _ => if Ascii.eqb c ":"%char then option_map (cons (Word ":")) (lex_tp_fuel k rest) else None end
      else if existsb (Ascii.eqb c) ["("%char; ")"%char; ";"%char; ","%char]
        then option_map (cons (Word (String c ""))) (lex_tp_fuel k rest) else None
    end
  end.
Definition lex_tp s := lex_tp_fuel (S (String.length s)) s.
Definition reserved s := existsb (String.eqb s) ["axiom";"def";"theorem";"import";"forall";"fun";"Type";"Kind"].
Definition name_token t := match t with
  | Word (String c _) => letter c && negb (reserved (match t with Word s => s | _ => "" end))
  | _ => false end.
Definition starts_atom t := match t with
  | Word s => String.eqb s "(" || String.eqb s "Type" || String.eqb s "Kind" || name_token t
  | _ => false end.
Definition consume s ts := match ts with
  | Word w :: rest => if String.eqb s w then Some rest else None | _ => None end.
Fixpoint parameter_names ts : list string * list tp_token :=
  match ts with
  | Word n :: rest => if name_token (Word n) then
      let '(ns,tail) := parameter_names rest in (n::ns,tail) else ([],ts)
  | _ => ([],ts) end.

(** Recursive descent with a byte-derived budget, independent of typing fuel.
    Each recursive edge decreases fuel; exhausted budgets reject input. *)
Fixpoint parse_term fuel ts : option (raw_expr * list tp_token) :=
  match fuel with 0 => None | S k =>
    match ts with
    | Word w :: rest =>
      if String.eqb w "forall" || String.eqb w "fun" then
        match parse_parameters k rest with
        | Some (PNil,_) => None
        | Some (ps,tail) => match consume (if String.eqb w "forall" then "," else "=>") tail with
          | Some tail => match parse_term k tail with
            | Some (b,tail) => Some ((if String.eqb w "forall" then RForall ps b else RLambda ps b),tail)
            | None => None end
          | None => None end
        | None => None end
      else match parse_atom k ts with
        | Some (a,tail) => match parse_application k a tail with
          | Some (a,tail) => match consume "->" tail with
            | Some tail => match parse_term k tail with
              | Some (b,tail) => Some (RArrow a b,tail) | None => None end
            | None => Some (a,tail) end
          | None => None end
        | None => None end
    | _ => None end
  end
with parse_atom fuel ts : option (raw_expr * list tp_token) :=
  match fuel with 0 => None | S k => match ts with
  | Word w :: rest =>
    if String.eqb w "Type" then Some (RType,rest) else
    if String.eqb w "Kind" then Some (RKind,rest) else
    if String.eqb w "(" then match parse_term k rest with
      | Some (e,tail) => match consume ")" tail with Some tail => Some (e,tail) | None => None end
      | None => None end
    else if name_token (Word w) then Some (RName w,rest) else None
  | _ => None end end
with parse_application fuel a ts : option (raw_expr * list tp_token) :=
  match fuel with 0 => None | S k => match ts with
  | t :: _ => if starts_atom t then match parse_atom k ts with
      | Some (b,tail) => parse_application k (RApply a b) tail | None => None end
    else Some (a,ts)
  | [] => Some (a,[]) end end
with parse_parameters fuel ts : option (parameters * list tp_token) :=
  match fuel with 0 => None | S k => match consume "(" ts with
  | None => Some (PNil,ts)
  | Some tail => match parameter_names tail with
    | ([],_) => None
    | (n::ns,tail) => match consume ":" tail with
      | Some tail => match parse_term k tail with
        | Some (a,tail) => match consume ")" tail with
          | Some tail => match parse_parameters k tail with
            | Some (ps,tail) => Some (PGroup n ns a ps,tail) | None => None end
          | None => None end
        | None => None end
      | None => None end end end end.

Inductive tp_item := TpDeclaration (d : raw_declaration) | TpImport (path : string).
Fixpoint parse_items_tp fuel ts : option (list tp_item) :=
  match fuel with 0 => None | S k => match ts with
  | [] => Some []
  | Word "import" :: Path p :: Word ";" :: tail =>
      if String.eqb p "" then None else option_map (cons (TpImport p)) (parse_items_tp k tail)
  | Word kind :: Word n :: tail =>
      if (String.eqb kind "axiom" || String.eqb kind "def" || String.eqb kind "theorem") && name_token (Word n) then
      match parse_parameters k tail with
      | Some (ps,tail) => match consume ":" tail with
        | Some tail => match parse_term k tail with
          | Some (a,tail) =>
            let body := if String.eqb kind "axiom" then Some (None,tail) else
              match consume ":=" tail with
              | Some tail => match parse_term k tail with
                | Some (b,tail) => Some (Some (RLambda ps b),tail) | None => None end
              | None => None end in
            match body with
            | Some (b,tail) => match consume ";" tail with
              | Some tail => option_map (cons (TpDeclaration (RawDecl n (RForall ps a) b))) (parse_items_tp k tail)
              | None => None end
            | None => None end
          | None => None end
        | None => None end
      | None => None end else None
  | _ => None end end.
Definition parse_tp s := match lex_tp s with
  | Some ts => parse_items_tp (S (4 * List.length ts)) ts | None => None end.
