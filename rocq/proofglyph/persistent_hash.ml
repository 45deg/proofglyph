(* Rerooting keeps the linear state-passing path cheap while preserving old
   versions. Hash collisions are resolved by the extracted equality function.
   Keys must be immutable, with hashes consistent with that equality. *)
type ('k, 'v) t = ('k, 'v) version ref
and ('k, 'v) version =
  | Root of (int, ('k * 'v) list) Hashtbl.t
  | Diff of int * ('k * 'v) list option * ('k, 'v) t

let empty () = ref (Root (Hashtbl.create 256))
let restore h key = function
  | None -> Hashtbl.remove h key
  | Some bucket -> Hashtbl.replace h key bucket

let reroot t =
  (* Iterative traversal also handles long-lived branches without stack growth. *)
  let path = ref [] and current = ref t in
  let searching = ref true in
  while !searching do
    match !(!current) with
    | Root _ -> searching := false
    | Diff (_, _, parent) -> path := !current :: !path; current := parent
  done;
  List.iter (fun node -> match !node with
    | Root _ -> ()
    | Diff (key, previous, parent) ->
        match !parent with
        | Diff _ -> assert false
        | Root h ->
            let newer = Hashtbl.find_opt h key in
            restore h key previous;
            node := Root h;
            parent := Diff (key, newer, node)) !path;
  match !t with Root h -> h | Diff _ -> assert false

let find_opt equal key t =
  let h = reroot t in
  match Hashtbl.find_opt h (Hashtbl.hash key) with
  | None -> None
  | Some bucket ->
      let rec find = function
        | [] -> None
        | (other, value) :: rest -> if equal key other then Some value else find rest
      in find bucket

let add key value t =
  let h = reroot t in
  let hash = Hashtbl.hash key in
  let previous = Hashtbl.find_opt h hash in
  let bucket = match previous with None -> [] | Some entries -> entries in
  Hashtbl.replace h hash ((key, value) :: bucket);
  let newer = ref (Root h) in
  t := Diff (hash, previous, newer);
  newer

let of_list entries = List.fold_right (fun (k, v) t -> add k v t) entries (empty ())
