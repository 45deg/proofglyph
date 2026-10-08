(* Untrusted generator: builds pa terms directly, without the tp compiler. *)
open Tinyprover_core
module Writer = Tinyprover_pa.Writer

type expr = Name of string | Sort | Apply of expr * expr
  | Product of string * expr * expr | Lambda of string * expr * expr
let n s = Name s
let app f xs = List.fold_left (fun f x -> Apply (f,x)) (n f) xs
let pi bs body = List.fold_right (fun (x,a) b -> Product (x,a,b)) bs body
let lam bs body = List.fold_right (fun (x,a) b -> Lambda (x,a,b)) bs body
let form = n "Formula"
let ctx = n "Context"
let nil = n "nil"
let cons a g = app "cons" [a;g]
let conn c a b = app c [a;b]
let neg a = app "Neg" [a]
let mem a g = app "InContext" [a;g]
let nk g a = app "NK" [g;a]
let lk g d = app "LK" [g;d]
let perm g h = app "Perm" [g;h]
let arrow a b = Product ("_",a,b)
let arrows xs b = List.fold_right arrow xs b
let a = n "A" and b = n "B" and c = n "C"
let g = n "G" and d = n "D" and h = n "H"
let fs xs = List.map (fun x -> x,form) xs
let cs xs = List.map (fun x -> x,ctx) xs

let rec rocq = function
  | Term.Type -> "tType" | Term.Kind -> "tKind"
  | Term.Var i -> Printf.sprintf "(tVar %d)" i
  | Term.Const i -> Printf.sprintf "(tConst %d)" i
  | Term.App (f,x) -> Printf.sprintf "(tApp %s %s)" (rocq f) (rocq x)
  | Term.Pi (a,b) -> Printf.sprintf "(tPi %s %s)" (rocq a) (rocq b)
  | Term.Lam (a,b) -> Printf.sprintf "(tLam %s %s)" (rocq a) (rocq b)

let () =
  if Array.length Sys.argv <> 2 then failwith "usage: export OUTPUT_DIR";
  let globals = ref [] and assumptions = ref [] and proofs = ref [] in
  let kernel = Kernel.create () in
  let rec resolve locals = function
    | Sort -> Term.Type
    | Name s ->
        let rec local i = function
          | [] -> Term.Const (List.assoc s !globals)
          | x::xs -> if x=s then Term.Var i else local (i+1) xs
        in local 0 locals
    | Apply (f,x) -> Term.App (resolve locals f,resolve locals x)
    | Product (x,a,b) -> Term.Pi (resolve locals a,resolve (x::locals) b)
    | Lambda (x,a,b) -> Term.Lam (resolve locals a,resolve (x::locals) b)
  in
  let add name typ body =
    if List.mem_assoc name !globals then failwith ("duplicate name: " ^ name);
    let typ = resolve [] typ in
    let body = Option.map (resolve []) body in
    let id = try (match body with None -> Kernel.assume kernel typ
      | Some t -> Kernel.prove kernel typ t) with Kernel.Error msg ->
        failwith (name ^ ": " ^ msg) in
    globals := !globals @ [name,id];
    let entry = name,typ,body in
    match body with None -> assumptions := !assumptions @ [entry]
      | Some _ -> proofs := !proofs @ [entry]
  in
  let assume name bs typ = add name (pi bs typ) None in
  let rule name bs premises conclusion = assume name bs (arrows premises conclusion) in
  assume "Index" [] Sort;
  assume "zero" [] (n "Index");
  assume "succ" [] (arrow (n "Index") (n "Index"));
  assume "Formula" [] Sort;
  assume "Atom" [] (arrow (n "Index") form);
  assume "Bottom" [] form; assume "Top" [] form;
  List.iter (fun s -> assume s [] (arrows [form;form] form)) ["Imp";"Conj";"Disj"];
  assume "Neg" [] (arrow form form);
  assume "Context" [] Sort; assume "nil" [] ctx;
  assume "cons" [] (arrows [form;ctx] ctx);
  assume "InContext" [] (arrows [form;ctx] Sort);
  rule "in_here" (fs ["A"] @ cs ["G"]) [] (mem a (cons a g));
  rule "in_there" (fs ["A";"B"] @ cs ["G"]) [mem a g] (mem a (cons b g));
  assume "Perm" [] (arrows [ctx;ctx] Sort);
  rule "perm_nil" [] [] (perm nil nil);
  rule "perm_cons" (fs ["A"] @ cs ["G";"H"]) [perm g h] (perm (cons a g) (cons a h));
  rule "perm_swap" (fs ["A";"B"] @ cs ["G"]) []
    (perm (cons a (cons b g)) (cons b (cons a g)));
  rule "perm_trans" (cs ["G";"H";"D"]) [perm g h;perm h d] (perm g d);
  assume "NK" [] (arrows [ctx;form] Sort);
  let ng xs = cs ["G"] @ fs xs in
  rule "nk_assume" (ng ["A"]) [mem a g] (nk g a);
  rule "nk_top" (cs ["G"]) [] (nk g (n "Top"));
  rule "nk_bottom" (ng ["A"]) [nk g (n "Bottom")] (nk g a);
  rule "nk_imp_intro" (ng ["A";"B"]) [nk (cons a g) b] (nk g (conn "Imp" a b));
  rule "nk_imp_elim" (ng ["A";"B"]) [nk g (conn "Imp" a b);nk g a] (nk g b);
  rule "nk_conj_intro" (ng ["A";"B"]) [nk g a;nk g b] (nk g (conn "Conj" a b));
  rule "nk_conj_left" (ng ["A";"B"]) [nk g (conn "Conj" a b)] (nk g a);
  rule "nk_conj_right" (ng ["A";"B"]) [nk g (conn "Conj" a b)] (nk g b);
  rule "nk_disj_left" (ng ["A";"B"]) [nk g a] (nk g (conn "Disj" a b));
  rule "nk_disj_right" (ng ["A";"B"]) [nk g b] (nk g (conn "Disj" a b));
  rule "nk_disj_elim" (ng ["A";"B";"C"])
    [nk g (conn "Disj" a b);nk (cons a g) c;nk (cons b g) c] (nk g c);
  rule "nk_neg_intro" (ng ["A"]) [nk (cons a g) (n "Bottom")] (nk g (neg a));
  rule "nk_neg_elim" (ng ["A"]) [nk g (neg a);nk g a] (nk g (n "Bottom"));
  rule "nk_classical" (ng ["A"]) [nk (cons (neg a) g) (n "Bottom")] (nk g a);
  assume "LK" [] (arrows [ctx;ctx] Sort);
  let lg xs = cs ["G";"D"] @ fs xs in
  rule "lk_identity" (fs ["A"]) [] (lk (cons a nil) (cons a nil));
  rule "lk_bottom" (cs ["G";"D"]) [] (lk (cons (n "Bottom") g) d);
  rule "lk_top" (cs ["G";"D"]) [] (lk g (cons (n "Top") d));
  rule "lk_weak_left" (lg ["A"]) [lk g d] (lk (cons a g) d);
  rule "lk_weak_right" (lg ["A"]) [lk g d] (lk g (cons a d));
  rule "lk_contract_left" (lg ["A"]) [lk (cons a (cons a g)) d] (lk (cons a g) d);
  rule "lk_contract_right" (lg ["A"]) [lk g (cons a (cons a d))] (lk g (cons a d));
  rule "lk_exchange_left" (cs ["G";"H";"D"]) [perm g h;lk g d] (lk h d);
  rule "lk_exchange_right" (cs ["G";"H";"D"]) [perm d h;lk g d] (lk g h);
  rule "lk_imp_right" (lg ["A";"B"]) [lk (cons a g) (cons b d)] (lk g (cons (conn "Imp" a b) d));
  rule "lk_imp_left" (lg ["A";"B"]) [lk g (cons a d);lk (cons b g) d]
    (lk (cons (conn "Imp" a b) g) d);
  rule "lk_conj_left" (lg ["A";"B"]) [lk (cons a (cons b g)) d]
    (lk (cons (conn "Conj" a b) g) d);
  rule "lk_conj_right" (lg ["A";"B"]) [lk g (cons a d);lk g (cons b d)]
    (lk g (cons (conn "Conj" a b) d));
  rule "lk_disj_left" (lg ["A";"B"]) [lk (cons a g) d;lk (cons b g) d]
    (lk (cons (conn "Disj" a b) g) d);
  rule "lk_disj_right" (lg ["A";"B"]) [lk g (cons a (cons b d))]
    (lk g (cons (conn "Disj" a b) d));
  rule "lk_neg_left" (lg ["A"]) [lk g (cons a d)] (lk (cons (neg a) g) d);
  rule "lk_neg_right" (lg ["A"]) [lk (cons a g) d] (lk g (cons (neg a) d));
  rule "lk_cut" (lg ["A"]) [lk g (cons a d);lk (cons a g) d] (lk g d);
  let prove name bs typ body = add name (pi bs typ) (Some (lam bs body)) in
  let hyp g a = app "nk_assume" [g;a;app "in_here" [a;nil]] in
  prove "nk_identity" (fs ["A"]) (nk nil (conn "Imp" a a))
    (app "nk_imp_intro" [nil;a;a;hyp (cons a nil) a]);
  let ab = conn "Conj" a b in
  prove "nk_conj_comm" (fs ["A";"B"]) (nk nil (conn "Imp" ab (conn "Conj" b a)))
    (app "nk_imp_intro" [nil;ab;conn "Conj" b a;
      app "nk_conj_intro" [cons ab nil;b;a;
        app "nk_conj_right" [cons ab nil;a;b;hyp (cons ab nil) ab];
        app "nk_conj_left" [cons ab nil;a;b;hyp (cons ab nil) ab]]]);
  let em = conn "Disj" a (neg a) in
  let ng = cons (neg em) nil in
  let ag = cons a ng in
  let ar = app "nk_assume" [ag;a;app "in_here" [a;ng]] in
  let nem = app "nk_assume" [ag;neg em;app "in_there" [neg em;a;ng;app "in_here" [neg em;nil]]] in
  let na = app "nk_neg_intro" [ng;a;app "nk_neg_elim" [ag;em;nem;app "nk_disj_left" [ag;a;neg a;ar]]] in
  prove "nk_excluded_middle" (fs ["A"]) (nk nil em)
    (app "nk_classical" [nil;em;app "nk_neg_elim" [ng;em;hyp ng (neg em);
      app "nk_disj_right" [ng;a;neg a;na]]]);
  let ident a = app "lk_identity" [a] in
  prove "lk_imp_identity" (fs ["A"]) (lk nil (cons (conn "Imp" a a) nil))
    (app "lk_imp_right" [nil;nil;a;a;ident a]);
  prove "lk_excluded_middle" (fs ["A"]) (lk nil (cons em nil))
    (app "lk_disj_right" [nil;nil;a;neg a;
      app "lk_exchange_right" [nil;cons a (cons (neg a) nil);cons (neg a) (cons a nil);
        app "perm_swap" [neg a;a;nil];app "lk_neg_right" [nil;cons a nil;a;ident a]]]);
  prove "lk_cut_identity" (fs ["A"]) (lk (cons a nil) (cons a nil))
    (app "lk_cut" [cons a nil;cons a nil;a;
      app "lk_weak_right" [cons a nil;cons a nil;a;ident a];
      app "lk_weak_left" [cons a nil;cons a nil;a;ident a]]);
  let write name contents =
    let ch = open_out_bin (Filename.concat Sys.argv.(1) name) in
    Fun.protect ~finally:(fun () -> close_out_noerr ch) (fun () -> output_string ch contents)
  in
  let pa (_,a,b) = Writer.encode a ^ (match b with None -> ":\n"
    | Some t -> Writer.encode t ^ "!\n") in
  let declaration (_,a,b) = match b with None -> "Assume " ^ rocq a
    | Some t -> "Prove " ^ rocq a ^ " " ^ rocq t in
  let list xs = "[\n  " ^ String.concat ";\n  " (List.map declaration xs) ^ "\n]" in
  write "prelude.pa" (String.concat "" (List.map pa !assumptions));
  write "proofs.pa" (String.concat "" (List.map pa !proofs));
  write "names.txt" (String.concat "\n" (List.map fst !globals) ^ "\n");
  write "Artifact.v" ("From Stdlib Require Import List.\nFrom Rocq4pa Require Import Syntax Program.\nImport ListNotations.\nDefinition prelude : list declaration := " ^ list !assumptions
    ^ ".\nDefinition proofs : list declaration := " ^ list !proofs ^ ".\n");
  Printf.printf "exported %d fixed assumptions and %d proofs directly to pa\n"
    (List.length !assumptions) (List.length !proofs)
