module C = Checker
module R = Cache_reference
let nat = Z.of_int
let require condition message = if not condition then failwith message
let rec reference = function
  | C.TType -> R.TType | C.TKind -> R.TKind
  | C.TVar n -> R.TVar n | C.TConst n -> R.TConst n
  | C.TPi (a,b) -> R.TPi (reference a, reference b)
  | C.TLam (a,b) -> R.TLam (reference a, reference b)
  | C.TApp (a,b) -> R.TApp (reference a, reference b)
let rec cached = function
  | R.TType -> C.TType | R.TKind -> C.TKind
  | R.TVar n -> C.TVar n | R.TConst n -> C.TConst n
  | R.TPi (a,b) -> C.TPi (cached a, cached b)
  | R.TLam (a,b) -> C.TLam (cached a, cached b)
  | R.TApp (a,b) -> C.TApp (cached a, cached b)

let persistent_tables () =
  let random = Random.State.make [|713|] in
  let versions = ref [Persistent_hash.empty (), []] in
  for _ = 1 to 1500 do
    let old, model = List.nth !versions (Random.State.int random (List.length !versions)) in
    let k = Random.State.int random 40 and v = Random.State.int random 1000 in
    let newer = Persistent_hash.add k v old in
    require (Persistent_hash.find_opt (=) k old = List.assoc_opt k model) "insert changed old version";
    versions := (newer, (k,v)::model) :: !versions;
    for _ = 1 to 8 do
      let table, model = List.nth !versions (Random.State.int random (List.length !versions)) in
      let key = Random.State.int random 40 in
      require (Persistent_hash.find_opt (=) key table = List.assoc_opt key model) "branched version mismatch"
    done
  done;
  let from_list = Persistent_hash.of_list [1,10;1,20;2,30] in
  require (Persistent_hash.find_opt (=) 1 from_list = Some 10) "first binding lost";
  let old = Persistent_hash.empty () in
  let next = ref old in
  for i = 1 to 50000 do next := Persistent_hash.add i i !next done;
  require (Persistent_hash.find_opt (=) 50000 old = None) "long history changed old version";
  require (Persistent_hash.find_opt (=) 50000 !next = Some 50000) "long history lost latest value";
  let prefix = List.init 64 (fun _ -> C.TType) in
  let key0 = prefix @ [C.TConst (nat 0)], C.TVar (nat 0) in
  let key1 = prefix @ [C.TConst (nat 1)], C.TVar (nat 0) in
  require (Hashtbl.hash key0 = Hashtbl.hash key1) "collision fixture no longer collides";
  let table = Persistent_hash.add key1 C.TKind (Persistent_hash.add key0 C.TType (Persistent_hash.empty ())) in
  require (Persistent_hash.find_opt C.cache_key_eq key0 table = Some C.TType) "hash collision confused keys";
  require (Persistent_hash.find_opt C.cache_key_eq key1 table = Some C.TKind) "hash collision lost value";
  let huge = Z.shift_left Z.one 100 in
  let key = [C.TVar huge], C.TConst (Z.succ huge) in
  let equivalent = [C.TVar (Z.of_string (Z.to_string huge))], C.TConst (Z.of_string (Z.to_string (Z.succ huge))) in
  let table = Persistent_hash.add key C.TType (Persistent_hash.empty ()) in
  require (Persistent_hash.find_opt C.cache_key_eq equivalent table = Some C.TType) "Zarith key hashing disagrees with equality"

let inference () =
  let random = Random.State.make [|1729|] in
  let rec term depth =
    let shape = Random.State.int random (if depth = 0 then 4 else 7) in
    match shape with
    | 0 -> C.TType | 1 -> C.TKind
    | 2 -> C.TVar (nat (Random.State.int random 4))
    | 3 -> C.TConst (nat (Random.State.int random 4))
    | 4 -> C.TPi (term (depth-1), term (depth-1))
    | 5 -> C.TLam (term (depth-1), term (depth-1))
    | _ -> C.TApp (term (depth-1), term (depth-1))
  in
  let signatures = [ []; [C.TType]; [C.TType;C.TConst (nat 0)];
    [C.TType;C.TPi (C.TConst (nat 0), C.TConst (nat 0));C.TConst (nat 0)] ] in
  List.iter (fun sg ->
    let table = ref (C.table_empty ()) in
    for _ = 1 to 600 do
      let ctx = List.init (Random.State.int random 4) (fun _ -> term 1) in
      let t = term 3 in
      List.iter (fun fuel ->
        let expected = R.infer (nat fuel) (List.map reference sg) (List.map reference ctx) (reference t)
          |> Option.map cached in
        let result = C.infer (nat fuel) sg ctx t !table in
        require (Option.map fst result = expected) "cached inference changed fuel/result";
        match result with None -> () | Some (_, next) -> table := next)
        [20;1;0;8;20]
    done) signatures;
  let table = ref (C.table_empty ()) in
  let misses = ref 0 in
  let compute cache = incr misses; Some (C.TKind, cache) in
  let key = [], C.TType in
  let first = C.memoize (nat 1) key !table compute in
  table := snd (Option.get first);
  for _ = 1 to 100 do ignore (C.memoize (nat 1) key !table compute) done;
  require (!misses = 1) "cache hits recomputed inference";
  let failed_key = [], C.TKind in
  ignore (C.memoize (nat 1) failed_key !table (fun _ -> None));
  require (C.table_lookup C.cache_key_eq failed_key !table = None) "failed result entered cache"

let benchmark () =
  let a = C.TConst (nat 0) in
  let sg = [C.TType; C.TPi (a, C.TPi (a,a)); a] in
  let rec shared depth = if depth = 0 then C.TConst (nat 2) else
    let child = shared (depth-1) in C.TApp (C.TApp (C.TConst (nat 1), child), child) in
  let t = shared 12 in
  let rs = List.map reference sg and rt = reference t in
  let measure run =
    Gc.full_major (); let start = Sys.time () in
    for _ = 1 to 8 do run () done;
    Sys.time () -. start in
  let uncached = measure (fun () -> require (R.infer (nat 100) rs [] rt = Some (reference a)) "reference benchmark rejected") in
  let cached = measure (fun () -> require
    (Option.map fst (C.infer (nat 100) sg [] t (C.table_empty ())) = Some a) "cached benchmark rejected") in
  Printf.printf "Repeated-subterm benchmark (8 runs, depth 12): uncached %.4fs, cached %.4fs\n%!" uncached cached

let () =
  persistent_tables (); inference (); benchmark ();
  print_endline "Persistent hash versions, collisions, large keys, cache hits and 12000 inference comparisons passed"
