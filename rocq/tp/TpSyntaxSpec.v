From Stdlib Require Import List String Ascii Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.
From Tinyprover.Tp Require Export DesugarSpec.

Definition letter c := let n := nat_of_ascii c in
  ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)) || (n =? 95).
Definition ident c := letter c ||
  ((48 <=? nat_of_ascii c) && (nat_of_ascii c <=? 57)) || (nat_of_ascii c =? 39).
Definition whitespace c := existsb (Ascii.eqb c) [" "%char; "009"%char; "010"%char; "013"%char].
Inductive tp_token := Word (s : string) | Path (s : string).
Definition reserved s := existsb (String.eqb s) ["axiom";"def";"theorem";"import";"forall";"fun";"Type";"Kind"].
Definition name_token t := match t with
  | Word (String c _) => letter c && negb (reserved (match t with Word s => s | _ => "" end))
  | _ => false end.
Definition starts_atom t := match t with
  | Word s => String.eqb s "(" || String.eqb s "Type" || String.eqb s "Kind" || name_token t
  | _ => false end.
Inductive tp_item := TpDeclaration (d : raw_declaration) | TpImport (path : string).

(** Token grammar with explicit stopping conditions for greedy application
    and parameter groups. None of these relations mentions a parser or fuel. *)
Definition token_at word ts tail := ts = Word word :: tail.
Definition not_at word ts := forall tail, ~ token_at word ts tail.
Inductive names_prefix : list tp_token -> list string -> list tp_token -> Prop :=
| names_end : forall ts,
    (forall n rest, ts = Word n::rest -> name_token (Word n) = false) ->
    names_prefix ts [] ts
| names_more : forall n rest ns tail,
    name_token (Word n) = true -> names_prefix rest ns tail ->
    names_prefix (Word n::rest) (n::ns) tail.

Inductive term_parses : list tp_token -> raw_expr -> list tp_token -> Prop :=
| term_binder : forall w ts ps tail body b final,
    String.eqb w "forall" || String.eqb w "fun" = true ->
    parameters_parse ts ps tail -> ps <> PNil ->
    token_at (if String.eqb w "forall" then "," else "=>") tail body ->
    term_parses body b final ->
    term_parses (Word w::ts) (if String.eqb w "forall" then RForall ps b else RLambda ps b) final
| term_plain : forall ts a after_atom out tail,
    atom_parses ts a after_atom -> application_parses a after_atom out tail ->
    not_at "->" tail -> term_parses ts out tail
| term_arrow : forall ts a after_atom left tail right final,
    atom_parses ts a after_atom -> application_parses a after_atom left (Word "->"::tail) ->
    term_parses tail right final -> term_parses ts (RArrow left right) final
with atom_parses : list tp_token -> raw_expr -> list tp_token -> Prop :=
| atom_type : forall tail, atom_parses (Word "Type"::tail) RType tail
| atom_kind : forall tail, atom_parses (Word "Kind"::tail) RKind tail
| atom_name : forall n tail, name_token (Word n) = true ->
    atom_parses (Word n::tail) (RName n) tail
| atom_parens : forall ts e tail, term_parses ts e (Word ")"::tail) ->
    atom_parses (Word "("::ts) e tail
with application_parses : raw_expr -> list tp_token -> raw_expr -> list tp_token -> Prop :=
| application_end : forall a ts,
    (forall t rest, ts = t::rest -> starts_atom t = false) -> application_parses a ts a ts
| application_more : forall a ts b tail out final,
    atom_parses ts b tail -> application_parses (RApply a b) tail out final ->
    application_parses a ts out final
with parameters_parse : list tp_token -> parameters -> list tp_token -> Prop :=
| parameters_end : forall ts, not_at "(" ts -> parameters_parse ts PNil ts
| parameters_group : forall ts n ns after_names a after_type ps tail,
    names_prefix ts (n::ns) (Word ":"::after_names) ->
    term_parses after_names a (Word ")"::after_type) ->
    parameters_parse after_type ps tail ->
    parameters_parse (Word "("::ts) (PGroup n ns a ps) tail.
Scheme term_parses_ind' := Induction for term_parses Sort Prop
with atom_parses_ind' := Induction for atom_parses Sort Prop
with application_parses_ind' := Induction for application_parses Sort Prop
with parameters_parse_ind' := Induction for parameters_parse Sort Prop.
Combined Scheme syntax_ind from term_parses_ind', atom_parses_ind', application_parses_ind', parameters_parse_ind'.

Definition declaration_keyword w := String.eqb w "axiom" || String.eqb w "def" || String.eqb w "theorem".
Inductive body_parses (kind : string) (ps : parameters) :
    list tp_token -> option raw_expr -> list tp_token -> Prop :=
| body_axiom : forall ts, kind = "axiom" -> body_parses kind ps ts None ts
| body_proof : forall ts b tail, kind <> "axiom" -> term_parses ts b tail ->
    body_parses kind ps (Word ":="::ts) (Some (RLambda ps b)) tail.
Inductive items_parse : list tp_token -> list tp_item -> Prop :=
| items_parse_nil : items_parse [] []
| items_parse_import : forall path ts items, path <> "" -> items_parse ts items ->
    items_parse (Word "import"::Path path::Word ";"::ts) (TpImport path::items)
| items_parse_decl : forall kind n ts ps after_ps a after_type body after_body rest items,
    declaration_keyword kind = true -> name_token (Word n) = true ->
    parameters_parse ts ps after_ps -> token_at ":" after_ps after_type ->
    term_parses after_type a after_body ->
    body_parses kind ps after_body body (Word ";"::rest) ->
    items_parse rest items ->
    items_parse (Word kind::Word n::ts)
      (TpDeclaration (RawDecl n (RForall ps a) body)::items).

(** Byte classification is part of the lexical language specification. *)
Inductive byte_role := SpaceByte | SlashByte | LetterByte | QuoteByte | PairByte | PunctuationByte | InvalidByte.
Definition byte_class c :=
  if whitespace c then SpaceByte else if Ascii.eqb c "/"%char then SlashByte else
  if letter c then LetterByte else if Ascii.eqb c """"%char then QuoteByte else
  if existsb (Ascii.eqb c) [":"%char; "-"%char; "="%char] then PairByte else
  if existsb (Ascii.eqb c) ["("%char; ")"%char; ";"%char; ","%char] then PunctuationByte else InvalidByte.
Definition pair_symbol c d :=
  (Ascii.eqb c ":"%char && Ascii.eqb d "="%char) ||
  ((Ascii.eqb c "-"%char || Ascii.eqb c "="%char) && Ascii.eqb d ">"%char).
Definition pair_stops c rest := match rest with
  | EmptyString => True | String d _ => pair_symbol c d = false end.
Definition path_forbidden c := existsb (Ascii.eqb c) ["010"%char; "013"%char; "\"%char].
Inductive maximal_span (p : ascii -> bool) : string -> string -> string -> Prop :=
| span_empty : maximal_span p "" "" ""
| span_stop : forall c rest, p c = false -> maximal_span p (String c rest) "" (String c rest)
| span_more : forall c rest prefix suffix, p c = true -> maximal_span p rest prefix suffix ->
    maximal_span p (String c rest) (String c prefix) suffix.
Inductive quoted_path : string -> string -> string -> Prop :=
| quoted_close : forall suffix, quoted_path (String """"%char suffix) "" suffix
| quoted_more : forall c rest path suffix,
    Ascii.eqb c """"%char = false -> path_forbidden c = false ->
    quoted_path rest path suffix -> quoted_path (String c rest) (String c path) suffix.
Inductive lexical_step : string -> option tp_token -> string -> Prop :=
| lex_space : forall c rest, byte_class c = SpaceByte -> lexical_step (String c rest) None rest
| lex_comment : forall c rest prefix suffix,
    byte_class c = SlashByte -> maximal_span (fun x => negb (Ascii.eqb x "010"%char)) rest prefix suffix ->
    lexical_step (String c (String "/"%char rest)) None suffix
| lex_word : forall c rest prefix suffix,
    byte_class c = LetterByte -> maximal_span ident rest prefix suffix ->
    lexical_step (String c rest) (Some (Word (String c prefix))) suffix
| lex_path : forall c rest path suffix,
    byte_class c = QuoteByte -> quoted_path rest path suffix ->
    lexical_step (String c rest) (Some (Path path)) suffix
| lex_pair : forall c d rest,
    byte_class c = PairByte -> pair_symbol c d = true ->
    lexical_step (String c (String d rest)) (Some (Word (String c (String d "")))) rest
| lex_colon : forall c rest,
    byte_class c = PairByte -> Ascii.eqb c ":"%char = true -> pair_stops c rest ->
    lexical_step (String c rest) (Some (Word ":")) rest
| lex_punctuation : forall c rest,
    byte_class c = PunctuationByte -> lexical_step (String c rest) (Some (Word (String c ""))) rest.
Inductive tp_lexes : string -> list tp_token -> Prop :=
| tp_lex_empty : tp_lexes "" []
| tp_lex_skip : forall bytes suffix ts,
    lexical_step bytes None suffix -> tp_lexes suffix ts -> tp_lexes bytes ts
| tp_lex_token : forall bytes suffix t ts,
    lexical_step bytes (Some t) suffix -> tp_lexes suffix ts -> tp_lexes bytes (t::ts).
Definition tp_parses bytes items := exists ts, tp_lexes bytes ts /\ items_parse ts items.
