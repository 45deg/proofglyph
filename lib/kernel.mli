exception Error of string
type origin = Assumption | Proven
type entry = { typ : Term.t; origin : origin }
type t
val create : ?fuel:int -> unit -> t
val entries : t -> entry list
val infer : t -> Term.t -> Term.t
val assume : t -> Term.t -> int
val prove : t -> Term.t -> Term.t -> int
