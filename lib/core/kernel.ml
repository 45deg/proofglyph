open Term

(** Raised when type checking fails or the verification budget (fuel) is exhausted. *)
exception Error of string

(** Provenance of a registered constant. *)
type origin = Assumption | Proven

(** Entry for a registered constant in the signature. *)
type entry = { typ : Term.t; origin : origin }

(** Internal kernel state.
    - [signature]: list of registered constants in registration order.
    - [fuel]: remaining computation budget preventing infinite loops. *)
type t = { mutable signature : entry list; mutable fuel : int }

(** Initializes a new kernel instance.
    Default fuel is 1,000,000 steps. *)
let create ?(fuel=1_000_000) () =
  if fuel < 1 then invalid_arg "fuel must be positive";
  { signature=[]; fuel }

(** Returns the list of registered constants. *)
let entries k = k.signature

(** Error helper function. *)
let fail s = raise (Error s)

(** Consumes one verification step (fuel). Fails immediately when fuel is exhausted. *)
let tick k =
  if k.fuel <= 0 then fail "verification budget exhausted";
  k.fuel <- k.fuel - 1

(** Bounds-checked list access handling negative or out-of-bounds indices. *)
let nth xs n message =
  if n < 0 then fail message;
  match List.nth_opt xs n with Some x -> x | None -> fail message

(** Weak Head Normal Form (WHNF) reduction.
    Evaluates the head of an application if it is a lambda abstraction (β-reduction),
    without reducing inside unapplied lambda bodies or arguments. *)
let rec whnf k t =
  tick k;
  match t with
  | App (f,x) -> (match whnf k f with
      | Lam (_,body) -> whnf k (instantiate body x)
      | f -> App (f,x))
  | t -> t

(** Full β-normalization.
    Reduces the term to WHNF and recursively normalizes all subterms (Pi, Lam, App). *)
let rec normal k t =
  match whnf k t with
  | Pi (a,b) -> Pi (normal k a, normal k b)
  | Lam (a,b) -> Lam (normal k a, normal k b)
  | App (f,x) -> App (normal k f, normal k x)
  | t -> t

(** Tests β-equivalence.
    Normalizes both sides to full β-normal form and performs structural syntactic comparison.
    Since de Bruijn indices are used, α-equivalence corresponds to syntactic equality.
    Note: neither η-equivalence nor constant unfolding is supported. *)
let equal k a b = a = b || normal k a = normal k b

(** Type inference for term [t] under local context [ctx].
    Enforces LF / λΠ typing rules:
    - [Type] : [Kind]
    - [Kind] has no type (prevents Type:Type paradox)
    - Variable [Var n] fetches type from [ctx] and shifts it to the current depth
    - Constant [Const n] fetches its type from the signature (opaque)
    - [Pi (a,b)] is well-formed when [a : Type] and [ctx, x:a |- b : s] where [s ∈ {Type, Kind}]
    - [Lam (a,b)] is well-typed when [a : Type] and [infer(b)] is not [Kind]
    - [App (f,x)] has type [b[x/0]] when [f] has type [Pi (a,b)] and [x] has type β-equivalent to [a] *)
let rec infer_in k ctx t =
  tick k;
  match t with
  | Type -> Kind
  | Kind -> fail "Kind has no type"
  | Var n -> shift (n+1) 0 (nth ctx n "unbound variable")
  | Const n -> (nth k.signature n "unknown constant").typ
  | Pi (a,b) ->
      if sort k ctx a <> Type then fail "Pi domain must have sort Type";
      sort k (a::ctx) b
  | Lam (a,b) ->
      if sort k ctx a <> Type then fail "lambda domain must have sort Type";
      (* In a well-formed context, an inferred type other than Kind has a sort,
         so the Pi type does not need to be checked again. *)
      (match infer_in k (a::ctx) b with
       | Kind -> fail "Kind has no type"
       | body_type -> Pi (a,body_type))
  | App (f,x) ->
      (match whnf k (infer_in k ctx f) with
       | Pi (a,b) ->
           let actual = infer_in k ctx x in
           if not (equal k actual a) then fail "application argument type mismatch";
           instantiate b x
       | _ -> fail "application requires a Pi type")

(** Infers the type of [t] and verifies that it is a sort ([Type] or [Kind]), returning that sort. *)
and sort k ctx t =
  match whnf k (infer_in k ctx t) with
  | (Type | Kind) as s -> s
  | _ -> fail "expected a type or kind"

(** Infers the type of [t] in the empty context. *)
let infer k t = infer_in k [] t

(** Internal helper to append a constant to the signature and return its assigned index. *)
let add k origin typ =
  let id = List.length k.signature in
  k.signature <- k.signature @ [{typ;origin}]; id

(** Registers an axiom/assumption after checking that [typ] is well-formed in the empty context. *)
let assume k typ =
  ignore (sort k [] typ); add k Assumption typ

(** Verifies a proof term and registers it as a proven constant.
    1. Checks that [typ] is well-formed in the empty context.
    2. Infers the type of [term] in the empty context.
    3. Verifies that the inferred type is β-equivalent to [typ].
    4. Upon success, records the constant as [Proven] (the proof term itself is not stored). *)
let prove k typ term =
  ignore (sort k [] typ);
  let actual = infer k term in
  if not (equal k actual typ) then fail "proof type mismatch";
  add k Proven typ
