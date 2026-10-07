open Term
exception Error of string
type origin = Assumption | Proven
type entry = { typ : Term.t; origin : origin }
type t = { mutable signature : entry list; mutable fuel : int }
let create ?(fuel=1_000_000) () =
  if fuel < 1 then invalid_arg "fuel must be positive";
  { signature=[]; fuel }
let entries k = k.signature
let fail s = raise (Error s)
let tick k =
  if k.fuel <= 0 then fail "verification budget exhausted";
  k.fuel <- k.fuel - 1
let nth xs n message =
  if n < 0 then fail message;
  match List.nth_opt xs n with Some x -> x | None -> fail message
let rec whnf k t =
  tick k;
  match t with
  | App (f,x) -> (match whnf k f with
      | Lam (_,body) -> whnf k (instantiate body x)
      | f -> App (f,x))
  | t -> t
let rec normal k t =
  match whnf k t with
  | Pi (a,b) -> Pi (normal k a, normal k b)
  | Lam (a,b) -> Lam (normal k a, normal k b)
  | App (f,x) -> App (normal k f, normal k x)
  | t -> t
let equal k a b = normal k a = normal k b
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
      let result = Pi (a,infer_in k (a::ctx) b) in
      ignore (sort k ctx result); result
  | App (f,x) ->
      (match whnf k (infer_in k ctx f) with
       | Pi (a,b) ->
           let actual = infer_in k ctx x in
           if not (equal k actual a) then fail "application argument type mismatch";
           instantiate b x
       | _ -> fail "application requires a Pi type")
and sort k ctx t =
  match whnf k (infer_in k ctx t) with
  | (Type | Kind) as s -> s
  | _ -> fail "expected a type or kind"
let infer k t = infer_in k [] t
let add k origin typ =
  let id = List.length k.signature in
  k.signature <- k.signature @ [{typ;origin}]; id
let assume k typ =
  ignore (sort k [] typ); add k Assumption typ
let prove k typ term =
  ignore (sort k [] typ);
  let actual = infer k term in
  if not (equal k actual typ) then fail "proof type mismatch";
  add k Proven typ
