(** Persistent versions of an OCaml hash table. Operations may reroot internal
    storage, but all observable lookups on older versions remain unchanged. *)
type ('k, 'v) t
val empty : unit -> ('k, 'v) t
val of_list : ('k * 'v) list -> ('k, 'v) t
val find_opt : ('k -> 'k -> bool) -> 'k -> ('k, 'v) t -> 'v option
val add : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t
