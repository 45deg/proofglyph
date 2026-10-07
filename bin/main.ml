open Tinyprover_core
module Assembly = Tinyprover_pa.Reader
module Source = Tinyprover_tp.Source

(** {1 tinyprover CLI Entry Point}

    Command-line interface implementation:
    - [compile]: Compiles a .tp source file into verified .pa assembly and optional sourcemap.
    - [check]: Verifies a .pa assembly file against the kernel.
    - [inspect]: Verifies a .pa assembly file and prints each constant's type and provenance.

    Exit codes:
    - 0: Success
    - 1: Verification, syntax, I/O, or resource failure (fuel exhaustion, stack overflow)
    - 2: Command-line usage error *)

(** Reads an entire file into a string in binary mode. *)
let read path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch))

(** Writes binary data to a file path. *)
let write path data =
  let ch = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () -> output_string ch data)

(** Prints usage instructions to stderr and exits with status 2. *)
let usage () =
  prerr_endline "Usage: tinyprover (compile SOURCE [-o FILE] [--sourcemap FILE] | check ASSEMBLY [--prelude FILE] [--no-axioms] | inspect ASSEMBLY) [--fuel N]";
  exit 2

let () =
  try
    if Array.length Sys.argv < 3 then usage ();
    let command = Sys.argv.(1) and path = Sys.argv.(2) in
    let output = ref None and prelude = ref None and no_axioms = ref false in
    let sourcemap = ref None in
    let fuel = ref 1_000_000 in
    let rec options i = if i < Array.length Sys.argv then (
      let value () = if i+1 >= Array.length Sys.argv then usage (); Sys.argv.(i+1) in
      match Sys.argv.(i) with
      | "-o" -> output := Some(value()); options (i+2)
      | "--sourcemap" -> sourcemap := Some(value()); options (i+2)
      | "--prelude" -> prelude := Some(value()); options (i+2)
      | "--fuel" -> fuel := int_of_string (value()); options (i+2)
      | "--no-axioms" -> no_axioms := true; options (i+1)
      | _ -> usage ())
    in options 3;
    if !fuel < 1 then invalid_arg "fuel must be positive";
    (match command with
     | "compile" ->
         (* compile: parse and expand source, compile to assembly, self-verify through kernel *)
         if !prelude <> None || !no_axioms then usage ();
         (match !output, !sourcemap with
          | Some a, Some b ->
              let identity p =
                try let st = Unix.stat p in `Existing (st.Unix.st_dev, st.Unix.st_ino)
                with Unix.Unix_error (Unix.ENOENT,_,_) ->
                  `New (Unix.realpath (Filename.dirname p), Filename.basename p) in
              if identity a = identity b then
                invalid_arg "assembly and sourcemap output paths must differ"
          | _ -> ());
          let result = Source.compile_file ~fuel:!fuel path in
          Option.iter (fun p -> write p (Source.sourcemap_json result)) !sourcemap;
          (match !output with None -> print_string result.assembly | Some p -> write p result.assembly)
     | "check" | "inspect" ->
         (* check / inspect: parse assembly and verify through an independent kernel *)
         if !output <> None || !sourcemap <> None then usage ();
         if command="inspect" && (!prelude<>None || !no_axioms) then usage ();
         let k = Kernel.create ~fuel:!fuel () in
         (* Execute prelude first if present (axioms allowed) *)
         Option.iter (fun p -> Assembly.run k (read p)) !prelude;
         (* Execute target assembly; forbid axioms (:) if --prelude or --no-axioms is active *)
         Assembly.run ~allow_axioms:(not !no_axioms && !prelude=None) k (read path);
         let entries = Kernel.entries k in
         List.iteri (fun i (e:Kernel.entry) ->
           Printf.printf "c%d [%s] : %s\n" i
             (match e.origin with Kernel.Assumption -> "assumption" | Kernel.Proven -> "proven")
             (Term.pretty e.typ)) entries;
         Printf.printf "Accepted: %d declarations (%d assumptions).\n" (List.length entries)
           (List.length (List.filter (fun (e:Kernel.entry) -> e.origin=Kernel.Assumption) entries))
     | _ -> usage ())
  with
  | Kernel.Error s | Assembly.Error s | Source.Error s -> prerr_endline ("error: " ^ s); exit 1
  | Sys_error s | Failure s | Invalid_argument s -> prerr_endline ("error: " ^ s); exit 1
  | Unix.Unix_error (e,_,p) -> prerr_endline ("error: " ^ p ^ ": " ^ Unix.error_message e); exit 1
  | Stack_overflow -> prerr_endline "error: nesting exceeds runtime stack capacity"; exit 1
