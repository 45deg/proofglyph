module S = Tinyprover_tp.Source
module T = Tinyprover_core.Term
module F = Frontend

let rec term = function
  | T.Type -> F.TType | T.Kind -> F.TKind
  | T.Var n -> F.TVar (Adapter.nat_of_int n)
  | T.Const n -> F.TConst (Adapter.nat_of_int n)
  | T.Pi (a, b) -> F.TPi (term a, term b)
  | T.Lam (a, b) -> F.TLam (term a, term b)
  | T.App (f, x) -> F.TApp (term f, term x)

(* Independent implementation used only as a differential test oracle. *)
let reference ds =
  let rec go globals index = function
    | [] -> []
    | (d : S.declaration) :: rest ->
        if List.mem_assoc d.name globals then failwith "duplicate reference declaration";
        let a = term (S.resolve globals d.at d.typ) in
        let d' = match d.body with
          | None -> F.Assume a
          | Some b -> F.Prove (a, term (S.resolve globals d.at b))
        in
        d' :: go ((d.name, index) :: globals) (index + 1) rest
  in go [] 0 ds

let fuel = Adapter.nat_of_int 2048

let reference_bytes ds =
  let globals = ref [] in
  let declarations = List.mapi (fun index (d : S.declaration) ->
    let encode e = Tinyprover_pa.Writer.encode (S.resolve !globals d.at e) in
    let a = encode d.typ in
    let bytes = match d.body with None -> a ^ ":" | Some b -> a ^ encode b ^ "!" in
    globals := (d.name, index) :: !globals;
    bytes) ds
  in String.concat "" declarations

let compare label ds =
  let source = Adapter.declarations ds in
  let expected = reference ds in
  if F.lower [] source <> Some expected then failwith (label ^ ": translation mismatch");
  match F.compile fuel true source with
  | None -> failwith (label ^ ": rejected")
  | Some (actual, signature) ->
      if actual <> expected then failwith (label ^ ": checked declaration mismatch");
      if signature <> List.map F.declared_type expected then failwith (label ^ ": signature mismatch");
      let bytes = F.encode_pa actual in
      if Adapter.string_of_chars bytes <> reference_bytes ds then failwith (label ^ ": encoded bytes mismatch");
      if F.decode_pa bytes <> Some actual then failwith (label ^ ": byte roundtrip failed");
      if F.compile_pa fuel true source <> Some (bytes, signature) then failwith (label ^ ": byte compilation failed");
      if F.check_pa fuel true bytes <> Some signature then failwith (label ^ ": encoded bytes rejected");
      Tinyprover_pa.Reader.run (Tinyprover_core.Kernel.create ()) (Adapter.string_of_chars bytes)

let codec_fixtures () =
  let decode s = F.decode_pa (Adapter.chars s) in
  let n = Adapter.nat_of_int in
  let raw = [F.Assume F.TKind;
    F.Prove (F.TPi (F.TType, F.TVar (n 12)),
      F.TLam (F.TConst (n 345), F.TApp (F.TVar (n 0), F.TConst (n 999))))] in
  if decode (Adapter.string_of_chars (F.encode_pa raw)) <> Some raw then failwith "raw codec roundtrip";
  if decode "$0012#0345@:" <> Some [F.Assume (F.TApp (F.TVar (n 12), F.TConst (n 345)))] then
    failwith "maximal digits / leading zeroes";
  if decode "\t*\n\r : " <> Some [F.Assume F.TType] then failwith "whitespace tokens";
  if decode "^:" <> Some [F.Assume F.TKind] then failwith "decoder performed type checking";
  if F.check_pa fuel true (Adapter.chars "^:") <> None then failwith "bad type accepted by check-pa";
  if decode " \n\t\r" <> Some [] then failwith "whitespace-only program";
  List.iter (fun s -> if decode s <> None then failwith ("malformed pa accepted: " ^ String.escaped s))
    ["#"; "$"; "#:"; "$ :"; "#-1:"; "# 1:"; "$1 2:"; "1:";
     ">"; "\\"; "@"; "*:!"; "**:"; "***!"; "*"; "*:*";
     ":"; "!"; "*:?"; "*:\000"; "*:\011"; "*:\012"; "*://comment"];
  (* Deterministic raw terms cover every constructor, decimal boundaries and
     combinations that need not be well typed. Codec laws do not require typing. *)
  let atoms = [T.Type; T.Kind] @ List.concat_map (fun i -> [T.Var i; T.Const i])
    [0; 1; 9; 10; 99; 100; 999; 1000] in
  let terms = atoms @ List.concat_map (fun a -> List.concat_map (fun b ->
    [T.Pi (a, b); T.Lam (a, b); T.App (a, b)]) atoms) atoms in
  List.iter (fun t ->
    let ds = [F.Assume (term t); F.Prove (term t, term (T.Lam (T.Type, t)))] in
    let bytes = F.encode_pa ds in
    if F.decode_pa bytes <> Some ds then failwith "generated raw term roundtrip";
    let expected = Tinyprover_pa.Writer.encode t ^ ":" ^ Tinyprover_pa.Writer.encode t ^
      Tinyprover_pa.Writer.encode (T.Lam (T.Type, t)) ^ "!" in
    if Adapter.string_of_chars bytes <> expected then failwith "generated raw term writer mismatch") terms;
  Printf.printf "Codec fixtures and %d raw term cases passed\n" (List.length terms)

let fixtures = [
  "dependent arrow", "axiom A : Type; axiom B : A -> Type; def f (x : A) : B x -> B x := fun (y : B x) => y;";
  "shadowing", "axiom A : Type; def f (x : A) (x : A) : A := x;";
  "global shadowing", "axiom A : Type; def f (A : A) : A := A;";
  "grouped parameter scope", "axiom A : Type; axiom B : A -> Type; def f (x : A) (x y : B x) : B x := y;";
  "underscore name", "axiom A : Type; def f (_ : A) : A := _;";
  "beta conversion", "axiom A : Type; axiom a : A; def f : (fun (x : A) => A) a := a;";
]

let () =
  codec_fixtures ();
  (* These two shadowing examples are intentionally not well typed, but their
     AST translations must still agree before the checker rejects them. *)
  List.iter (fun (label, source) ->
    let ds = S.parse source in
    if F.lower [] (Adapter.declarations ds) <> Some (reference ds) then
      failwith (label ^ ": translation mismatch")) fixtures;
  List.iter (fun (label, source) -> compare label (S.parse source))
    (List.filter (fun (label, _) -> label <> "global shadowing" && label <> "grouped parameter scope") fixtures);
  let bad_names = [
    "axiom a : A; axiom A : Type;";
    "axiom A : A;";
    "axiom A : Type; axiom A : Type;";
    "axiom A : Type; def f : A := missing;"
  ] in
  List.iter (fun source ->
    if F.lower [] (Adapter.declarations (S.parse source)) <> None then failwith "bad name accepted") bad_names;
  List.iter (fun source ->
    if F.compile fuel true (Adapter.declarations (S.parse source)) <> None then failwith "ill-typed program accepted")
    ["axiom bad : Kind;"; "axiom bad : forall (A : Type), A -> A;";
     "axiom A : Type; def bad : A := Type;"];
  let axiom = Adapter.declarations (S.parse "axiom A : Type;") in
  if F.compile fuel false axiom <> None then failwith "axiom policy ignored";
  if F.compile F.O true axiom <> None then failwith "zero fuel accepted";
  if F.compile fuel false [] <> Some ([], []) then failwith "empty program rejected";
  Array.iteri (fun i path -> if i > 0 then compare path (S.load path)) Sys.argv;
  Printf.printf "Frontend fixtures and %d imported .tp files passed\n" (Array.length Sys.argv - 1)
