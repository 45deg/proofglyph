open Tinyprover
let read path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch))
let write path data =
  let ch = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out ch) (fun () -> output_string ch data)
let usage () =
  prerr_endline "Usage: tinyprover (compile SOURCE [-o FILE] | check ASSEMBLY [--prelude FILE] [--no-axioms] | inspect ASSEMBLY) [--fuel N]";
  exit 2
let () =
  try
    if Array.length Sys.argv < 3 then usage ();
    let command = Sys.argv.(1) and path = Sys.argv.(2) in
    let output = ref None and prelude = ref None and no_axioms = ref false in
    let fuel = ref 1_000_000 in
    let rec options i = if i < Array.length Sys.argv then (
      let value () = if i+1 >= Array.length Sys.argv then usage (); Sys.argv.(i+1) in
      match Sys.argv.(i) with
      | "-o" -> output := Some(value()); options (i+2)
      | "--prelude" -> prelude := Some(value()); options (i+2)
      | "--fuel" -> fuel := int_of_string (value()); options (i+2)
      | "--no-axioms" -> no_axioms := true; options (i+1)
      | _ -> usage ())
    in options 3;
    if !fuel < 1 then invalid_arg "fuel must be positive";
    (match command with
     | "compile" ->
         if !prelude <> None || !no_axioms then usage ();
         let result = Source.compile_file ~fuel:!fuel path in
         (match !output with None -> print_string result.assembly | Some p -> write p result.assembly)
     | "check" | "inspect" ->
         if !output <> None then usage ();
         if command="inspect" && (!prelude<>None || !no_axioms) then usage ();
         let k = Kernel.create ~fuel:!fuel () in
         Option.iter (fun p -> Assembly.run k (read p)) !prelude;
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
  | Stack_overflow -> prerr_endline "error: nesting exceeds runtime stack capacity"; exit 1
