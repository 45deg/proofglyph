open Tinyprover_core
module Assembly = Tinyprover_pa.Reader
module Source = Tinyprover_tp.Source
open Term

(** {1 tinyprover Regression Test Suite}

    Covers unit and regression tests for kernel type checking, assembly execution,
    the .tp frontend compiler, import resolution, and mathematical libraries
    (propositional/predicate logic, equality, Peano arithmetic, and Fermat's Little Theorem).
    Also includes extensive negative test cases ensuring ill-formed inputs are rejected. *)

let count = ref 0

(** Runs a test assertion, printing [ok NN <name>] on success. *)
let test name f =
  incr count;
  try f (); Printf.printf "ok %02d %s\n" !count name
  with exn -> Printf.eprintf "FAIL %s: %s\n" name (Printexc.to_string exn); exit 1

(** Asserts that function [f] raises an error (Kernel/Assembly/Source [Error]). *)
let rejects f =
  let rejected = try f (); false with
    | Kernel.Error _ | Assembly.Error _ | Source.Error _ -> true in
  if not rejected then failwith "invalid input accepted"

let compile s = Source.compile s
let verify s = Assembly.run (Kernel.create ()) s

(** Asserts that compiling source string [s] is rejected with an error. *)
let reject_source s = rejects (fun () -> ignore (compile s))
let () =
  test "exact identity encoding" (fun () ->
    let r = compile "axiom A : Type; def id (x : A) : A := x;" in
    assert (r.assembly="*:\n#0#0>#0$0\\!\n"); verify r.assembly);
  test "sourcemap records exact declaration byte ranges and locations" (fun () ->
    let r = compile "// comment\n  axiom A : Type;\n\ndef id (x : A) : A := x;" in
    (match r.sourcemap with
     | [a; b] ->
         assert (a.constant = 0 && a.name = "A" && a.file = None);
         assert (a.line = 2 && a.column = 3 && a.start_byte = 0 && a.end_byte = 2);
         assert (b.constant = 1 && b.name = "id" && b.line = 4 && b.column = 1);
         assert (b.start_byte = 3 && b.end_byte = String.length r.assembly - 1);
         assert (String.sub r.assembly b.start_byte (b.end_byte - b.start_byte)
           = "#0#0>#0$0\\!")
     | _ -> assert false);
    assert ((compile "").sourcemap = []);
    assert (Source.sourcemap_json (compile "") = "{\"version\":1,\"mappings\":[\n\n]}\n");
    assert (Source.json_string "a\"\\\n\t\000" = "\"a\\\"\\\\\\u000a\\u0009\\u0000\""));
  test "sourcemap annotates diagnostics only inside declaration ranges" (fun () ->
    let compiled = compile "axiom A : Type;\ndef id (x : A) : A := x;" in
    let m = List.nth compiled.sourcemap 1 in
    let message = Printf.sprintf "byte %d: proof type mismatch" (m.end_byte - 1) in
    assert (Source.annotate_assembly_error compiled.sourcemap message
      = "2:1 (id): " ^ message);
    assert (Source.annotate_assembly_error compiled.sourcemap "byte 2: unknown instruction"
      = "byte 2: unknown instruction");
    assert (Source.annotate_assembly_error compiled.sourcemap "byte 999: unfinished stack"
      = "byte 999: unfinished stack");
    assert (Source.annotate_assembly_error compiled.sourcemap "other error" = "other error");
    let with_file = [{m with file = Some "examples/test.tp"}] in
    assert (Source.annotate_assembly_error with_file message
      = "examples/test.tp:2:1 (id): " ^ message));
  test "source type errors retain declaration location and assembly byte" (fun () ->
    match compile "// heading\naxiom A : Type;\ndef bad : A := Type;" with
    | _ -> assert false
    | exception Source.Error message ->
        assert (String.starts_with ~prefix:"3:1 (bad): byte " message));
  test "two binder index" (fun () ->
    let r = compile "axiom A : Type; def keep (x y : A) : A := x;" in
    assert (r.assembly="*:\n#0#0#0>>#0#0$1\\\\!\n"));
  test "dependent identity" (fun () ->
    ignore (compile "axiom A : Type; axiom B : A -> Type; def id (x : A) (y : B x) : B x := y;"));
  test "anonymous arrow shifts outer variable" (fun () ->
    ignore (compile "axiom A : Type; axiom B : A -> Type; def f (x : A) : B x -> B x := fun (y : B x) => y;"));
  test "beta conversion in types" (fun () ->
    ignore (compile "axiom A : Type; axiom B : A -> Type; axiom a : A; axiom b : B a; def t : (fun (x : A) => B x) a := b;"));
  test "dependent application substitutes under binder" (fun () ->
    ignore (compile "axiom A : Type; axiom B : A -> Type; axiom a : A; def f (x : A) (y : B x) : B x := y; def g : B a -> B a := f a;"));
  test "forall and right associative arrow" (fun () ->
    ignore (compile "axiom A : Type; def k : forall (x : A), A -> A := fun (x y : A) => x;"));
  test "local shadowing" (fun () ->
    ignore (compile "axiom A : Type; def f (x : A) (x : A) : A := x;"));
  test "comments and whitespace" (fun () ->
    ignore (compile "// test\naxiom A:Type; // end"); verify " * \n : ");
  test "reject Type in Type" (fun () -> reject_source "axiom U : Type; def bad : Type := Type;");
  test "reject Kind declaration" (fun () -> reject_source "axiom bad : Kind;");
  test "reject CoC product" (fun () -> reject_source "axiom bad : forall (A : Type), A -> A;");
  test "reject lambda returning Kind as type" (fun () ->
    let k=Kernel.create() in ignore(Kernel.assume k Type);
    rejects(fun () -> ignore(Kernel.infer k (Lam(Const 0,Type)))));
  test "reject lambda whose Pi body has type Kind" (fun () ->
    let k=Kernel.create() in ignore(Kernel.assume k Type);
    rejects(fun () -> ignore(Kernel.infer k (Lam(Const 0,Pi(Const 0,Type))))));
  test "lambda returning a type has a Pi type" (fun () ->
    let k=Kernel.create() in ignore(Kernel.assume k Type);
    assert(Kernel.infer k (Lam(Const 0,Const 0)) = Pi(Const 0,Type)));
  test "nested lambdas infer within a linear fuel budget" (fun () ->
    let k=Kernel.create ~fuel:400 () in ignore(Kernel.assume k Type);
    let rec lambdas n = if n=0 then Var 99 else Lam(Const 0,lambdas(n-1)) in
    let rec arrows n = if n=0 then Const 0 else Pi(Const 0,arrows(n-1)) in
    assert(Kernel.infer k (lambdas 100) = arrows 100));
  test "reject mismatched proof" (fun () -> reject_source "axiom A : Type; axiom B : Type; axiom a : A; def bad : B := a;");
  test "reject mismatched application" (fun () -> reject_source "axiom A : Type; axiom B : Type; axiom f : A -> A; axiom b : B; def bad : A := f b;");
  test "reject nonfunction application" (fun () -> reject_source "axiom A : Type; axiom a : A; def bad : A := a a;");
  test "reject illformed domain" (fun () -> reject_source "axiom A : Type; axiom a : A; axiom bad : a -> A;");
  test "reject open terms" (fun () -> rejects(fun () -> verify "$0:"));
  test "reject forward constant" (fun () -> rejects(fun () -> verify "#0:"));
  test "reject forward source name" (fun () -> reject_source "axiom x : A; axiom A : Type;");
  test "reject duplicate names" (fun () -> reject_source "axiom A : Type; axiom A : Type;");
  test "reject self reference" (fun () -> reject_source "axiom A : Type; def f : A := f;");
  test "opaque definitions do not reduce" (fun () ->
    reject_source "axiom A : Type; axiom B : A -> Type; axiom a : A; def id (x : A) : A := x; axiom b : B a; def bad : B (id a) := b;");
  test "index overflow" (fun () -> rejects(fun () -> verify "#999999999999999999999999999999:"));
  test "missing index" (fun () -> rejects(fun () -> verify "#:"));
  test "stack underflow" (fun () -> rejects(fun () -> verify "@"));
  test "registration exact stack" (fun () -> rejects(fun () -> verify "**:"));
  test "unfinished stack" (fun () -> rejects(fun () -> verify "*"));
  test "invalid opcode" (fun () -> rejects(fun () -> verify "?"));
  test "syntax failure" (fun () -> reject_source "axiom A Type;");
  test "fuel exhaustion fails closed" (fun () ->
    rejects(fun () -> Assembly.run (Kernel.create ~fuel:1 ()) "*:"));
  test "trusted prefix then proofs only" (fun () ->
    let k=Kernel.create() in Assembly.run k "*:";
    Assembly.run ~allow_axioms:false k "#0#0>#0$0\\!";
    rejects(fun () -> Assembly.run ~allow_axioms:false k "*:"));
  test "failed proof never registers" (fun () ->
    let k=Kernel.create() in ignore(Kernel.assume k Type);
    rejects(fun () -> ignore(Kernel.prove k (Const 0) Type));
    assert(List.length(Kernel.entries k)=1));
  test "capture avoiding substitution" (fun () ->
    assert(instantiate (Lam(Type,Var 1)) (Var 0) = Lam(Type,Var 1));
    assert(instantiate (Pi(Var 0,Var 2)) (Const 0) = Pi(Const 0,Var 1)));
  test "negative API indices rejected" (fun () ->
    rejects(fun () -> ignore(Kernel.infer (Kernel.create()) (Const (-1))));
    rejects(fun () -> ignore(Kernel.infer (Kernel.create()) (Var (-1)))));
  test "eta is not definitional equality" (fun () ->
    reject_source "axiom A : Type; axiom F : (A -> A) -> Type; axiom f : A -> A; axiom t : F f; def bad : F (fun (x : A) => f x) := t;");
  test "many depths preserve context types" (fun () ->
    for depth=1 to 30 do
      let k=Kernel.create() in ignore(Kernel.assume k Type);
      let rec arrows n = if n=0 then Const 0 else Pi(Const 0,arrows(n-1)) in
      let rec lambdas n b = if n=0 then b else Lam(Const 0,lambdas(n-1)b) in
      for index=0 to depth-1 do
        ignore(Kernel.prove k (arrows depth) (lambdas depth (Var index)))
      done
    done);
  let contains text fragment =
    let rec loop i = i + String.length fragment <= String.length text &&
      (String.sub text i (String.length fragment) = fragment || loop (i+1)) in
    loop 0 in
  let with_fixture files f =
    let dir = Filename.temp_file "tinyprover-import-" "" in
    Sys.remove dir; Unix.mkdir dir 0o700;
    let rec mkdir p = if not (Sys.file_exists p) then (mkdir (Filename.dirname p); Unix.mkdir p 0o700) in
    let write relative contents =
      let p = Filename.concat dir relative in
      mkdir (Filename.dirname p);
      let ch = open_out_bin p in
      Fun.protect ~finally:(fun () -> close_out ch) (fun () -> output_string ch contents) in
    let rec remove p =
      if (Unix.lstat p).Unix.st_kind = Unix.S_DIR then (
        Array.iter (fun name -> remove (Filename.concat p name)) (Sys.readdir p);
        Unix.rmdir p) else Sys.remove p in
    Fun.protect ~finally:(fun () -> remove dir) (fun () ->
      List.iter (fun (p,s) -> write p s) files;
      f dir write) in
  test "imports expand at their declaration site, relative to the importing file" (fun () ->
    with_fixture ["base.tp", "axiom A : Type;";
                  "nested dir/proof.tp", "import \"../base.tp\"; theorem id (x : A) : A := x;";
                  "root.tp", "import \"nested dir/proof.tp\"; theorem use (x : A) : A := id x;"]
      (fun dir _ ->
        let path = Filename.concat dir "root.tp" in
        let r = Source.compile_file path in
        assert (r.names = ["A"; "id"; "use"]); verify r.assembly;
        assert (List.map (fun (d:Source.declaration) -> Filename.basename (Option.get d.at.file))
          r.declarations = ["base.tp"; "proof.tp"; "root.tp"]);
        assert ((Source.compile_file path).assembly = r.assembly)));
  test "diamond imports and path aliases register one canonical file once" (fun () ->
    with_fixture ["base.tp", "axiom A : Type;";
                  "left.tp", "import \"base.tp\"; theorem left (x : A) : A := x;";
                  "right.tp", "import \"./base.tp\"; theorem right (x : A) : A := x;";
                  "root.tp", "import \"left.tp\"; import \"right.tp\"; import \"alias.tp\";"]
      (fun dir _ ->
        Unix.symlink "base.tp" (Filename.concat dir "alias.tp");
        let r = Source.compile_file (Filename.concat dir "root.tp") in
        assert (r.names = ["A"; "left"; "right"]);
        assert (List.map (fun (m:Source.mapping) ->
          Filename.basename (Option.get m.file)) r.sourcemap
          = ["base.tp"; "left.tp"; "right.tp"])));
  test "cyclic imports are rejected, including a symlink back to the root" (fun () ->
    with_fixture ["root.tp", "import \"other.tp\";"; "other.tp", "import \"root.tp\";"]
      (fun dir write ->
        rejects (fun () -> ignore (Source.compile_file (Filename.concat dir "root.tp")));
        write "root.tp" "import \"alias.tp\";";
        Unix.symlink "root.tp" (Filename.concat dir "alias.tp");
        rejects (fun () -> ignore (Source.compile_file (Filename.concat dir "root.tp")))));
  test "missing imports and imported source errors retain file locations" (fun () ->
    with_fixture ["root.tp", "import \"missing.tp\";"] (fun dir write ->
      let path = Filename.concat dir "root.tp" in
      (try ignore (Source.compile_file path); failwith "missing import accepted"
       with Source.Error msg -> assert (contains msg "root.tp:1:1"));
      write "missing.tp" "axiom A Type;";
      (try ignore (Source.compile_file path); failwith "invalid imported source accepted"
       with Source.Error msg -> assert (contains msg "missing.tp:1:"));
      write "missing.tp" "axiom A : Type;";
      assert ((Source.compile_file path).names = ["A"])));
  test "imports cannot hide duplicate declarations or forward references" (fun () ->
    with_fixture ["base.tp", "axiom A : Type;";
                  "root.tp", "axiom A : Type; import \"base.tp\";"]
      (fun dir write ->
        let path = Filename.concat dir "root.tp" in
        rejects (fun () -> ignore (Source.compile_file path));
        write "root.tp" "theorem id (x : A) : A := x; import \"base.tp\";";
        rejects (fun () -> ignore (Source.compile_file path))));
  test "import paths are quoted, nonempty and have no escapes" (fun () ->
    List.iter (fun s -> rejects (fun () -> ignore (Source.parse_items s)))
      ["import base;"; "import \"\";"; "import \"base.tp\"";
       "import \"bad\\path\";"; "import \"bad\npath\";"];
    reject_source "import \"base.tp\";");
  test "CLI preserves an existing output when an import or proof fails" (fun () ->
    with_fixture ["root.tp", "import \"missing.tp\";"; "out.pa", "sentinel"; "out.map", "map sentinel"]
      (fun dir write ->
        let root = Filename.concat dir "root.tp" and output = Filename.concat dir "out.pa" in
        let run () =
          let log = Unix.openfile (Filename.concat dir "log") [Unix.O_WRONLY;Unix.O_CREAT;Unix.O_TRUNC] 0o600 in
          let pid = Fun.protect ~finally:(fun () -> Unix.close log) (fun () ->
            Unix.create_process "../bin/main.exe"
              [|"tinyprover"; "compile"; root; "-o"; output; "--sourcemap"; Filename.concat dir "out.map"|] Unix.stdin log log) in
          assert (snd (Unix.waitpid [] pid) = Unix.WEXITED 1);
          assert (Source.read_file output = "sentinel");
          assert (Source.read_file (Filename.concat dir "out.map") = "map sentinel") in
        run ();
        write "root.tp" "axiom A : Type; theorem bad : A := Type;";
        run ()));
  let arithmetic_axioms = [
    "All"; "AllBi"; "AllNat"; "AllSeq"; "And"; "Cong";
    "Coprime"; "Divides"; "Eq"; "Even"; "Exists"; "False";
    "Imp"; "Le"; "Lt"; "Nat"; "Not"; "Odd";
    "Or"; "Prf"; "Prime"; "Prop"; "RationalRootTwo"; "U";
    "add"; "add_succ"; "add_zero"; "all_bi_elim"; "all_bi_intro"; "all_elim";
    "all_intro"; "all_nat_elim"; "all_nat_intro"; "all_seq_elim"; "all_seq_intro"; "and_intro";
    "and_left"; "and_right"; "choose"; "choose_pascal"; "choose_zero_column"; "choose_zero_row";
    "cong_elim"; "cong_intro"; "convolution"; "convolution_definition"; "coprime_elim"; "coprime_intro";
    "diagonal"; "diagonal_succ"; "diagonal_zero"; "divides_elim"; "divides_intro"; "eq_refl";
    "eq_subst"; "even_elim"; "even_intro"; "excluded_middle"; "exists_elim"; "exists_intro";
    "factorial"; "factorial_succ"; "factorial_zero"; "false_elim"; "imp_elim"; "imp_intro";
    "le_elim"; "le_intro"; "lt_elim"; "lt_intro"; "mul"; "mul_succ";
    "mul_zero"; "nat_induction"; "not_elim"; "not_intro"; "odd_elim"; "odd_intro";
    "or_elim"; "or_left"; "or_right"; "pow"; "pow_succ"; "pow_zero";
    "pred"; "pred_succ"; "pred_zero"; "prime_elim"; "prime_intro"; "rational_root_two_elim";
    "rational_root_two_intro"; "succ"; "succ_injective"; "succ_not_zero"; "sum"; "sum_between";
    "sum_between_succ_inside"; "sum_between_succ_outside"; "sum_between_zero"; "sum_succ"; "sum_zero"; "triangular";
    "triangular_succ"; "triangular_zero"; "zero";
  ] in
  (* Build the test catalog in memory; users import subject modules directly. *)
  let load_modules files =
    let seen = Hashtbl.create 256 in
    List.concat_map (fun file ->
      List.filter (fun (d:Source.declaration) ->
        let key = d.at.file, d.name in
        if Hashtbl.mem seen key then false
        else (Hashtbl.add seen key (); true)) (Source.load file)) files in
  let arithmetic_modules = [
    "../examples/commons/nat/addition.tp";
    "../examples/commons/nat/basic.tp";
    "../examples/commons/nat/binomial_coefficients.tp";
    "../examples/commons/nat/binomial_theorem.tp";
    "../examples/commons/nat/classical.tp";
    "../examples/commons/nat/congruence.tp";
    "../examples/commons/nat/convolution.tp";
    "../examples/commons/nat/diagonal.tp";
    "../examples/commons/nat/divisibility.tp";
    "../examples/commons/nat/division.tp";
    "../examples/commons/nat/euclid.tp";
    "../examples/commons/nat/factorization.tp";
    "../examples/commons/nat/fermat.tp";
    "../examples/commons/nat/induction.tp";
    "../examples/commons/nat/modular_sums.tp";
    "../examples/commons/nat/multiplication.tp";
    "../examples/commons/nat/order.tp";
    "../examples/commons/nat/ordered_multiplication.tp";
    "../examples/commons/nat/parity.tp";
    "../examples/commons/nat/powers.tp";
    "../examples/commons/nat/prime_binomial.tp";
    "../examples/commons/nat/prime_infinitude.tp";
    "../examples/commons/nat/primes.tp";
    "../examples/commons/nat/sqrt_two.tp";
    "../examples/commons/nat/sums.tp";
  ] in
  let logic_modules = ["../examples/commons/logic/propositional.tp";
    "../examples/commons/logic/quantifiers.tp"; "../examples/commons/logic/classical.tp"] in
  test "arithmetic signature contains only the fixed primitive foundation" (fun () ->
    let result = Source.compile_declarations (load_modules arithmetic_modules) in
    List.iter (fun (d:Source.declaration) ->
      if d.body = None then (
        assert (List.mem d.name arithmetic_axioms);
        assert (contains (Option.get d.at.file) "/examples/commons/foundation/"))
      else assert (contains (Option.get d.at.file) "/examples/commons/nat/")) result.declarations;
    List.iter (fun name ->
      let d = List.find (fun (d:Source.declaration) -> d.name = name) result.declarations in
      assert (d.body <> None)) ["convolution_zero"; "convolution_pascal"]);
  let reject_loaded declarations suffix =
    rejects (fun () -> ignore (Source.compile_declarations (declarations @ Source.parse suffix))) in
  let check_catalog files targets =
    let result = Source.compile_declarations (load_modules files) in
    let declarations = result.declarations in
    let k = Kernel.create () in Assembly.run k result.assembly;
    List.iter2 (fun (d:Source.declaration) (e:Kernel.entry) ->
      assert ((d.body = None) = (e.origin = Kernel.Assumption));
      if d.body = None then (
        let path = Option.get d.at.file in
        assert (contains path "/examples/commons/foundation/")))
      declarations (Kernel.entries k);
    List.iter (fun name ->
      let d = List.find (fun (d:Source.declaration) -> d.name = name) declarations in
      assert (d.body <> None)) targets;
    (* Move the fixed definition/rule signature to a prefix and compile again.
       All arithmetic axioms must be primitive rules or explicit definitions. *)
    let assumptions, proofs = List.partition (fun (d:Source.declaration) -> d.body = None) declarations in
    let replay = Source.compile_declarations (assumptions @ proofs) in
    let k = Kernel.create () in
    List.iter2 (fun (d:Source.declaration) line ->
      Assembly.run ~allow_axioms:(d.body = None) k line)
      replay.declarations (List.filter ((<>) "") (String.split_on_char '\n' replay.assembly));
    declarations in
  test "Fermat imports proved arithmetic prerequisites" (fun () ->
    let source = check_catalog ["../examples/fermat_application.tp"]
      ["fermat"; "fermat_sum"; "fermat_application"; "prime_mul_elim"; "prime_divides_choose";
       "choose_mul_identity"; "binomial_theorem"; "binomial_at_one";
       "sum_between_cong_zero"; "convolution_unit_right"] in
    reject_loaded source
      "theorem invalid_step (p x : Nat) (hp : Prf (Prime p)) : Prf (Cong (pow (succ x) p) (succ x) p) := fermat_step p x hp (cong_refl x p);" );
  test "logic catalog covers natural deduction and quantifiers" (fun () ->
    let source = check_catalog logic_modules
      ["implication_composition"; "exchange"; "duplicate"; "function_composition";
       "and_comm"; "and_assoc_forward"; "and_assoc_backward"; "or_comm"; "cases";
       "contraposition"; "demorgan_or_forward"; "demorgan_or_backward";
       "demorgan_and_forward"; "demorgan_and_backward";
       "forall_specialize"; "exists_witness"; "forall_to_exists"] in
    reject_loaded source (
      "\ntheorem invalid_and (A B : Prop) (h : Prf (And A B))"
      ^ " : Prf (And B A) := and_intro A B (and_left A B h) (and_right A B h);");
    reject_loaded source (
      "\ntheorem invalid_witness (P : U -> Prop) (x y : U) (h : Prf (P x))"
      ^ " : Prf (Exists P) := exists_witness P y h;"));
  test "constructive De Morgan directions need no excluded middle" (fun () ->
    let declarations = load_modules logic_modules in
    (* Re-encode the constructive fragment without either classical declaration. *)
    let globals = ref [] in
    let output = Buffer.create 256 in
    List.iter (fun (d:Source.declaration) ->
      if not (List.mem d.name ["excluded_middle"; "demorgan_and_forward"]) then (
        let typ = Source.resolve !globals d.at d.typ in
        Buffer.add_string output (Tinyprover_pa.Writer.encode typ);
        (match d.body with
         | None -> Buffer.add_char output ':'
         | Some b -> Buffer.add_string output (Tinyprover_pa.Writer.encode (Source.resolve !globals d.at b));
             Buffer.add_char output '!');
        globals := (d.name,List.length !globals)::!globals)) declarations;
    verify (Buffer.contents output));
  test "equality catalog derives laws from substitution" (fun () ->
    let source = check_catalog ["../examples/commons/equality.tp"] ["eq_sym"; "eq_trans"; "eq_cong"] in
    reject_loaded source (
      "\ntheorem invalid_sym (a b : U) (h : Prf (Eq a b)) : Prf (Eq b a) := h;"));
  test "arithmetic catalog covers natural numbers and number theory" (fun () ->
    let source = check_catalog arithmetic_modules
      ["add_zero_left"; "add_zero_right"; "add_assoc"; "add_comm";
       "mul_add_left"; "mul_add_right"; "mul_assoc"; "mul_comm"; "pow_add";
       "even_add"; "odd_add"; "triangular_double";
       "divides_trans"; "divides_add"; "divides_mul_right"; "divides_mul_left";
       "cong_add"; "cong_mul"; "cong_pow"; "prime_divides_choose";
       "binomial_theorem"; "primes_infinite"; "sqrt_two_irrational";
       "binomial_at_one"; "binomial_term_zero"; "binomial_middle_zero";
       "binomial_successor"; "fermat_step"; "fermat"; "fermat_sum";
       "one_succ"; "two_succ"; "prime_mul_elim"; "prime_not_divides_interior";
       "choose_mul_identity"; "convolution_ext"; "convolution_scale_left";
       "convolution_scale_right"; "prime_factor"; "factorial_successor_gt_one";
       "prime_bound_cases"; "factorial_divisor"; "divides_cancel_add";
       "prime_not_divides_one"; "prime_two"; "prime_positive"; "mul_cancel_left";
       "coprime_no_common_prime"; "sum_between_cong_zero"; "convolution_unit_right";
       "pow_zero_positive"; "sqrt_two_no_positive_fraction"; "convolution_zero"; "convolution_pascal"] in
    reject_loaded source (
      "\ntheorem invalid_binomial (a b n : Nat)"
      ^ " : Prf (Eq (pow (add a b) n)"
      ^ " (convolution n (fun (k : Nat) => pow a k) (fun (k : Nat) => pow b k)))"
      ^ " := binomial_theorem a b n;");
    reject_loaded source (
      "\ntheorem invalid_comm (a b : Nat) : Prf (Eq (add a b) (add b a))"
      ^ " := eq_refl (add a b);");
    reject_loaded source (
      "\ntheorem invalid_modulus (a b m n : Nat) (h : Prf (Cong a b m))"
      ^ " : Prf (Cong (pow a n) (pow b n) n) := cong_pow a b n n h;");
    reject_loaded source (
      "\ntheorem invalid_choose (p k : Nat) (hp : Prf (Prime p))"
      ^ " (hk : Prf (Lt zero k)) : Prf (Divides p (choose p k))"
      ^ " := prime_divides_choose p k hp hk hk;");
    reject_loaded source (
      "\ntheorem invalid_root (a b : Nat) (hc : Prf (Coprime a b))"
      ^ " (h : Prf (Eq (mul a a) (mul b b))) : Prf False"
      ^ " := sqrt_two_coprime_contradiction a b hc h;");
    reject_loaded source (
      "theorem invalid_descent (a b : Nat)"
      ^ " (h : Prf (Eq (mul a a) (mul (succ (succ zero)) (mul b b)))) : Prf False"
      ^ " := sqrt_two_no_positive_fraction a b (zero_lt_succ b) h;"));
  test "subject libraries compile independently" (fun () ->
    List.iter (fun path -> ignore (Source.compile_file path)) [
      "../examples/commons/equality.tp";
      "../examples/commons/foundation/arithmetic.tp";
      "../examples/commons/foundation/binomial.tp";
      "../examples/commons/foundation/classical.tp";
      "../examples/commons/foundation/congruence.tp";
      "../examples/commons/foundation/divisibility.tp";
      "../examples/commons/foundation/equality.tp";
      "../examples/commons/foundation/logic.tp";
      "../examples/commons/foundation/nat_logic.tp";
      "../examples/commons/foundation/order.tp";
      "../examples/commons/foundation/parity.tp";
      "../examples/commons/foundation/peano.tp";
      "../examples/commons/foundation/primes.tp";
      "../examples/commons/foundation/quantifiers.tp";
      "../examples/commons/foundation/sqrt_two.tp";
      "../examples/commons/foundation/sums.tp";
      "../examples/commons/logic/classical.tp";
      "../examples/commons/logic/propositional.tp";
      "../examples/commons/logic/quantifiers.tp";
      "../examples/commons/nat/addition.tp";
      "../examples/commons/nat/basic.tp";
      "../examples/commons/nat/binomial_coefficients.tp";
      "../examples/commons/nat/binomial_theorem.tp";
      "../examples/commons/nat/classical.tp";
      "../examples/commons/nat/congruence.tp";
      "../examples/commons/nat/convolution.tp";
      "../examples/commons/nat/diagonal.tp";
      "../examples/commons/nat/divisibility.tp";
      "../examples/commons/nat/division.tp";
      "../examples/commons/nat/euclid.tp";
      "../examples/commons/nat/factorization.tp";
      "../examples/commons/nat/fermat.tp";
      "../examples/commons/nat/induction.tp";
      "../examples/commons/nat/modular_sums.tp";
      "../examples/commons/nat/multiplication.tp";
      "../examples/commons/nat/order.tp";
      "../examples/commons/nat/ordered_multiplication.tp";
      "../examples/commons/nat/parity.tp";
      "../examples/commons/nat/powers.tp";
      "../examples/commons/nat/prime_binomial.tp";
      "../examples/commons/nat/prime_infinitude.tp";
      "../examples/commons/nat/primes.tp";
      "../examples/commons/nat/sqrt_two.tp";
      "../examples/commons/nat/sums.tp";
    ]);
  test "addition imports neither classical logic nor number theory" (fun () ->
    let declarations = Source.load "../examples/commons/nat/addition.tp" in
    List.iter (fun name ->
      assert (not (List.exists (fun (d:Source.declaration) -> d.name = name) declarations)))
      ["excluded_middle"; "Prime"; "convolution"; "RationalRootTwo"]);
  Printf.printf "%d tests passed.\n" !count
