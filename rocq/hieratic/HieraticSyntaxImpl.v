From Stdlib Require Import List String Ascii Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
From Proofglyph.Hieratic Require Export HieraticSyntaxSpec.

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
Definition next_chunk s : option (option hieratic_token * string) :=
  match s with
  | EmptyString => None
  | String c rest => match byte_class c with
    | SpaceByte => Some (None,rest)
    | SlashByte => match rest with
        | String d tail => if Ascii.eqb d "/"%char then
            Some (None,snd (span (fun x => negb (Ascii.eqb x "010"%char)) tail)) else None
        | _ => None end
    | LetterByte => let '(prefix,suffix) := span ident rest in
        Some (Some (Word (String c prefix)),suffix)
    | QuoteByte => match quoted rest with
        | Some (path,suffix) => Some (Some (Path path),suffix) | None => None end
    | PairByte => match rest with
        | String d tail => if pair_symbol c d then
            Some (Some (Word (String c (String d ""))),tail)
          else if Ascii.eqb c ":"%char then Some (Some (Word ":"),rest) else None
        | _ => if Ascii.eqb c ":"%char then Some (Some (Word ":"),rest) else None end
    | PunctuationByte => Some (Some (Word (String c "")),rest)
    | InvalidByte => None end
  end.
Fixpoint lex_hieratic_fuel (fuel : nat) (s : string) : option (list hieratic_token) :=
  match fuel with
  | 0 => None
  | S k => match s with
    | EmptyString => Some []
    | _ => match next_chunk s with
      | Some (None,suffix) => lex_hieratic_fuel k suffix
      | Some (Some token,suffix) => option_map (cons token) (lex_hieratic_fuel k suffix)
      | None => None end
    end
  end.
Definition lex_hieratic s := lex_hieratic_fuel (S (String.length s)) s.
Definition consume s ts := match ts with
  | Word w :: rest => if String.eqb s w then Some rest else None | _ => None end.
Fixpoint parameter_names ts : list string * list hieratic_token :=
  match ts with
  | Word n :: rest => if name_token (Word n) then
      let '(ns,tail) := parameter_names rest in (n::ns,tail) else ([],ts)
  | _ => ([],ts) end.

(** Recursive descent with a byte-derived budget, independent of typing fuel.
    Each recursive edge decreases fuel; exhausted budgets reject input. *)
Fixpoint parse_term fuel ts : option (raw_expr * list hieratic_token) :=
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
with parse_atom fuel ts : option (raw_expr * list hieratic_token) :=
  match fuel with 0 => None | S k => match ts with
  | Word w :: rest =>
    if String.eqb w "Type" then Some (RType,rest) else
    if String.eqb w "Kind" then Some (RKind,rest) else
    if String.eqb w "(" then match parse_term k rest with
      | Some (e,tail) => match consume ")" tail with Some tail => Some (e,tail) | None => None end
      | None => None end
    else if name_token (Word w) then Some (RName w,rest) else None
  | _ => None end end
with parse_application fuel a ts : option (raw_expr * list hieratic_token) :=
  match fuel with 0 => None | S k => match ts with
  | t :: _ => if starts_atom t then match parse_atom k ts with
      | Some (b,tail) => parse_application k (RApply a b) tail | None => None end
    else Some (a,ts)
  | [] => Some (a,[]) end end
with parse_parameters fuel ts : option (parameters * list hieratic_token) :=
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

Fixpoint parse_items_hieratic fuel ts : option (list hieratic_item) :=
  match fuel with 0 => None | S k => match ts with
  | [] => Some []
  | Word kind :: rest =>
    if String.eqb kind "import" then match rest with
    | Path p :: tail => if String.eqb p "" then None else
        match consume ";" tail with
        | Some tail => option_map (cons (HieraticImport p)) (parse_items_hieratic k tail)
        | None => None end
    | _ => None end else match rest with
    | Word n :: tail =>
      if declaration_keyword kind && name_token (Word n) then
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
              | Some tail => option_map (cons (HieraticDeclaration (RawDecl n (RForall ps a) b))) (parse_items_hieratic k tail)
              | None => None end
            | None => None end
          | None => None end
        | None => None end
      | None => None end else None
    | _ => None end
  | _ => None end end.
Definition parse_hieratic s := match lex_hieratic s with
  | Some ts => parse_items_hieratic (S (4 * List.length ts)) ts | None => None end.
