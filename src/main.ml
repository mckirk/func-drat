(*pp cppo *)

open Batteries
open Printf
open BatOptParse
open Types
open FlatArray

#include "debug.ml"

type redundancy_result = T | AT | RT | RAT | NotRedundant
type propagation_type = Core_first | Core_only | Non_core_only

let redundancy_to_str = (function
  | T -> "T"
  | AT -> "AT"
  | RT -> "RT"
  | RAT -> "RAT"
  | NotRedundant -> "not redundant")

let opt_parser = OptParser.make ~usage:"%prog cnf [options]" ()
let proof_file_opt = StdOpt.str_option ()
let all_clauses_file = StdOpt.str_option ()
let clause_core_file = StdOpt.str_option ()
let lemma_core_file  = StdOpt.str_option ()
let only_core_deletions  = StdOpt.store_true ()
let report_interval = StdOpt.float_option ()

let () =
  OptParser.add opt_parser
    ~help:"Path to proof file (defaults to [cnf_name].drat)"
    ~short_name:'p'
    ~long_name:"proof"
    proof_file_opt;

  OptParser.add opt_parser
    ~help:"Write all clauses and lemmas into given file after parsing"
    ~short_name:'w'
    ~long_name:"whole"
    all_clauses_file;

  OptParser.add opt_parser
    ~help:"Write core clauses into given file"
    ~short_name:'c'
    ~long_name:"core"
    clause_core_file;

  OptParser.add opt_parser
    ~help:"Write proof core into given file"
    ~short_name:'l'
    ~long_name:"lemmas"
    lemma_core_file;

  OptParser.add opt_parser
    ~help:"Skip deletions of non-core clauses in proof core"
    ~long_name:"core-deletions"
    only_core_deletions;

  OptParser.add opt_parser
    ~help:"Report progress every n seconds"
    ~short_name:'r'
    ~long_name:"report"
    report_interval

let start_time = ref 0.0
let verification_start_time = ref 0.0
let last_report_time = ref 0.0
let lemma_count = ref 0
let done_count = ref 0
let rat_count = ref 0
let set_start_time () =
  start_time := Sys.time ()
let set_verification_start_time () =
  let lemma_cnt, _ = State.get_lemma_stats () in
  let now = Sys.time () in
  verification_start_time := now;
  last_report_time := now;
  lemma_count := lemma_cnt
let lemma_done () =
  done_count := succ !done_count;
  if (!done_count mod 100 = 0) then begin
    let now = Sys.time () in
    if (now -. !last_report_time) >= (Opt.get report_interval) then begin
      let done_frac = (Float.of_int !done_count) /. (Float.of_int !lemma_count) in
      let time_remaining = (Sys.time () -. !verification_start_time) *. ((1.0 -. done_frac) /. done_frac) in
      printf "Verified %d of %d steps, estimated time to completion %.1f seconds\n%!" !done_count !lemma_count time_remaining;
      last_report_time := now
    end
  end
let had_rat_lemma () = rat_count := succ !rat_count
let print_stats () =
  let num_clauses, num_core_clauses = State.get_clause_stats () in
  let num_lemmas, num_core_lemmas = State.get_lemma_stats () in
  printf "Verification took %.3f seconds.\n" (Sys.time() -. !start_time);
  printf "%d/%d clauses, %d/%d lemmas in core\n" num_core_clauses num_clauses num_core_lemmas num_lemmas;
  printf "%d lemmas had RAT.\n%!" !rat_count

let parse_header header =
  (try Scanf.sscanf header "p cnf %d %d" State.set_problem_dimensions
    with End_of_file -> raise Error_wrong_input_syntax)

let no_comments str = not (String.is_empty str) && (str.[0] <> 'c')

let parse_cnf input_lines =
  let input_filtered = Enum.filter no_comments input_lines in
  (match Enum.get input_filtered with
  | Some header -> parse_header header
  | None -> raise Error_wrong_input_syntax);

  State.init_clause_memory ();

  Enum.iter (fun lits -> ignore @@ State.add_clause @@ Literals.from_string lits) input_filtered

let parse_proof proof_lines =
  let proof_filtered = Enum.filter no_comments proof_lines in

  let add_proof_step proof_line = (
    let parts = Str.split Misc.whitespace_regex proof_line in
    let new_proof_step = (
      match parts with
      | ["0"] -> Some ConflictClause
      | "d" :: elems -> (
          let literals = IntArray.of_array @@ Literals.from_string_list elems in
          try
            let found_clause = State.find_and_remove_hashed_clause literals in
            Some (DeletionIndex found_clause)
          with Not_found ->
            dprintf("Ignoring deletion of non-existent clause %s\n" (Literals.to_str literals));
            None)
      | (pivot_str :: _) as elems -> (
          let lemma_literals = Literals.from_string_list elems in
          let pivot = Literals.encode @@ String.to_int pivot_str in

          let lemma = State.add_clause lemma_literals in
          Some (LemmaIndex (lemma, pivot)))
      | [] -> raise (Error_invalid_proof ("Invalid line in proof: " ^ proof_line))) in
    match new_proof_step with
    | Some step -> ignore @@ ProofSteps.add step
    | None -> ()) in

  State.switch_to_lemmas (); (* finished adding clauses *)

  Enum.iter add_proof_step proof_filtered

let update_affected_clause clause_buf ~assign_callback changed_lit clause changed_pos =
  let other_pos = changed_pos lxor 1 in
  let other_lit = Clause.get_literal clause_buf clause other_pos in

  let assign_new_unit new_unit =
    dprintf("Found new unit %d\n" @@ Literals.decode new_unit);
    State.assign_true clause_buf new_unit clause;
    assign_callback () in

  dprintf("Updating clause %d: %s because of lit %d\n"
    (Clause.get_ID clause_buf clause) (Clause.to_str clause_buf clause) (Literals.decode changed_lit));

  dassert(Clause.get_literal clause_buf clause changed_pos = changed_lit);
  dassert(State.assigned_false changed_lit);

  if State.assigned_true other_lit then begin
    (* clause is satisfied, no conflict attainable *)
    dprintf("Already satisfied by lit %d\n" (Literals.decode other_lit))
  end else begin
    let changed_indexed = (changed_pos, changed_lit) in
    if not (State.assigned_false other_lit) then begin
      (* other watched literal is unassigned, maybe new unit *)
      match Clause.find_literal_index clause_buf clause State.unfalsified ~start:2 with
      | None -> assign_new_unit other_lit
      | Some nonfalse_indexed -> (* correct even if non-false literal is true *)
          State.move_watch clause_buf clause changed_indexed nonfalse_indexed
    end else begin
      (* both watched literals assigned false, we might have a conflict *)
      let other_indexed = (other_pos, other_lit) in
      match Clause.find_literal_index2 clause_buf clause State.unfalsified ~start:2 with
      | (None, _) -> raise (Found_conflict clause) (* all literals assigned false -> conflict *)
      | (Some ((_, new_unit) as nonfalse_indexed), None) -> (
          (* only one literal non-false, possibly new unit! *)
          (* remove watch from other lit early to save work *)
          State.move_watch clause_buf clause other_indexed nonfalse_indexed;
          if not @@ State.assigned_true new_unit then
            assign_new_unit new_unit)
      | (Some nonfalse_indexed1, Some nonfalse_indexed2) -> (
          State.move_watch clause_buf clause changed_indexed nonfalse_indexed1;
          State.move_watch clause_buf clause other_indexed   nonfalse_indexed2)
    end
  end

let rec propagate_units clause_buf prop_type =
  let callback_core = fun () -> () in
  let callback_noncore =
    (if prop_type = Core_first then
      fun () -> propagate_units clause_buf Core_only
    else
      fun () -> ()) in

  let process_literal_core lit =
    dprintf("Propagating literal core-only %d\n" @@ Literals.decode lit);
    State.iter_watch_clauses clause_buf
      Core
      (update_affected_clause clause_buf ~assign_callback:callback_core lit)
      lit;
    dprintf("Propagating for literal %d core-only ended\n\n" @@ Literals.decode lit) in

  let process_literal_noncore lit =
    dprintf("Propagating literal %d\n" @@ Literals.decode lit);
    State.iter_watch_clauses clause_buf
      Non_core
      (update_affected_clause clause_buf ~assign_callback:callback_noncore lit)
      lit;
    dprintf("Propagating for literal %d ended\n\n" @@ Literals.decode lit) in

  if prop_type = Core_first || prop_type = Core_only then
    State.iter_unprocessed_literals process_literal_core Core;
  if prop_type = Core_first || prop_type = Non_core_only then
    State.iter_unprocessed_literals process_literal_noncore Non_core

(* assumes the being-checked lemma's literals have already been assigned false and propagated (RUP check) *)
let check_rat clause_buf pivot clause =
  vprintf("Trying RAT against clause %s with pivot %d...\n" (Clause.to_str clause_buf clause) (Literals.decode pivot));
  let ignore_lit = Literals.negate pivot in
  try
    let process_literal lit =
      if lit <> ignore_lit then begin
        if State.assigned_true lit then
          raise (Blocked_clause lit)
        else if not @@ State.assigned_false lit then
          State.assign_false clause_buf lit Clause.no_reason (* no reason, temporary assignment *)
      end in

    Clause.iter_literals clause_buf clause process_literal;
    propagate_units clause_buf Core_first;
    vprintf("No RAT\n");
    false
  with
  | Blocked_clause lit ->
      let reason = State.get_falsification_reason (Literals.negate lit) in
      vprintf("Found blocked clause, lit %d, reason %d\n" (Literals.decode lit) (Clause.get_ID clause_buf reason));
      if reason <> Clause.no_reason then
        State.mark_as_core clause_buf reason;
      true
  | Found_conflict clause ->
      vprintf("Found RAT, conflict in clause %d\n" (Clause.get_ID clause_buf clause));
      State.mark_as_core clause_buf clause;
      true

let check_redundancy clause_buf lemma pivot =
  (* set all lits in lemma to false *)
  Clause.iter_literals clause_buf lemma
    (fun lit ->
      dassert(not @@ State.assigned_true lit); (* no tautologies *)
      if not @@ State.assigned_false lit then
        State.assign_false clause_buf lit Clause.no_reason);

  try
    propagate_units clause_buf Core_first;

    (* if no conflict, then no luck with RUP, trying RAT now *)
    let rat_candidates = State.get_rat_candidates clause_buf (Literals.negate pivot) in

    if List.for_all (fun c -> State.sandbox_assignment_effects clause_buf (fun () -> check_rat clause_buf pivot c)) rat_candidates
    then RAT
    else NotRedundant
  with Found_conflict clause -> (* lemma was RUP clause, no need to do anything more *)
    vprintf("Found RUP clause, conflict in clause %d\n" (Clause.get_ID clause_buf clause));
    dprintf("Trace for conflict: %s\n" (dump @@ State.get_conflict_trace clause_buf));
    State.mark_as_core clause_buf clause;
    AT

let verify_proof_step clause_buf = (function
| ConflictClause -> () (* we've already made sure the proof results in a conflict *)
| LemmaIndex (lemma, pivot) ->
    State.unreference_clause clause_buf lemma;

    let trail_before = Clause.get_trail_before_used clause_buf lemma in
    dassert(trail_before <> Trail.invalid_position);
    if trail_before <> State.get_trail_position () then begin
      dprintf("Rolling back trail to before lemma %d was used\n" (Clause.get_ID clause_buf lemma));
      State.backtrack_to_trail_position clause_buf trail_before
    end;

    if Clause.is_core clause_buf lemma then begin (* skip non-core lemmas entirely *)
      dprintf("Verifying lemma %s\n" (Clause.to_pretty_str clause_buf lemma));

      let redundancy = (match State.sandbox_assignment_effects clause_buf (fun () -> check_redundancy clause_buf lemma pivot) with
        | NotRedundant -> raise (Error_invalid_proof (sprintf "Lemma %s is not redundant!" (Clause.to_pretty_str clause_buf lemma)));
        | RAT -> had_rat_lemma (); RAT
        | x -> x) in
      vprintf("Verified lemma %d as %s\n%!" (Clause.get_ID clause_buf lemma) (redundancy_to_str redundancy))
    end else
      vprintf("Skipping lemma %d because it's non-core\n" (Clause.get_ID clause_buf lemma));

    if Opt.is_set report_interval then lemma_done ()
| DeletionIndex clause ->
    dprintf("Undeleting clause %s\n" (Clause.to_pretty_str clause_buf clause));
    State.reference_clause clause_buf clause)

let forward_pass clause_buf =
  let init_clause clause =
    match Clause.find_literal_index2 clause_buf clause State.unfalsified ~start:0 with
    | (None, _) -> raise Clause_already_falsified
    | (Some (i, lit), None) ->
        Clause.set_is_const_unit clause_buf clause true; (* clause already unit, will never have watches *)
        if not @@ State.assigned_true lit then begin
          State.assign_true clause_buf lit clause;
          propagate_units clause_buf Non_core_only
        end
    | (Some (i, lit1), Some (i2, lit2)) ->
        if i  <> 0 then Clause.swap_literals clause_buf clause 0 i;
        if i2 <> 1 then Clause.swap_literals clause_buf clause 1 i2;
        State.add_watch clause_buf (0, lit1) clause;
        State.add_watch clause_buf (1, lit2) clause in

  let init_proof_step = (function
  | LemmaIndex (lemma, _) ->
      (* save trail state for undoing assignments later *)
      Clause.set_trail_before_used clause_buf lemma @@ State.get_trail_position ();
      init_clause lemma
  | DeletionIndex clause ->
      if Clause.is_const_unit clause_buf clause then
        dprintf("Ignoring deletion of const-unit clause %s\n" (Clause.to_pretty_str clause_buf clause))
      else
        State.unreference_clause clause_buf clause
  | ConflictClause -> propagate_units clause_buf Non_core_only) in

  (try State.iter_clauses_only init_clause with
  | Clause_already_falsified | Found_conflict _ ->
      raise Trivially_unsat);

  puts "Added clauses, applying proof-steps now";

  let proof_steps_length = ProofSteps.get_length () in

  try
    for i = 0 to proof_steps_length - 1 do
      try init_proof_step @@ ProofSteps.step_by_index i with
      | Found_conflict clause ->
          State.mark_as_core clause_buf clause;
          raise (Found_conflict_step i)
      | Clause_already_falsified ->
          raise (Error_invalid_proof "Conflicting unit clauses in proof")
    done;
    raise (Error_invalid_proof "No conflict found in proof.")
  with Found_conflict_step step_idx ->
    printf "Found conflict in proof after step %d of %d\n" (step_idx+1) proof_steps_length;
    State.set_conflict_step step_idx

let verify_backward clause_buf =
  State.iter_steps_backwards_from_conflict ((verify_proof_step clause_buf) % ProofSteps.get)

#ifdef BACKTRACE
let () = Printexc.record_backtrace true
#endif

let () =
  try
    match OptParser.parse_argv opt_parser with
    | [input_file] ->
        let (input_name, ext) = String.rsplit input_file ~by:"." in
        let proof_file = Option.default (input_name ^ ".drat") (Opt.opt proof_file_opt) in

        set_start_time ();

        let input_lines = File.lines_of input_file in
        let proof_lines = File.lines_of proof_file in

        parse_cnf input_lines;
        puts "Parsed problem";
        parse_proof proof_lines;
        puts "Parsed proof";

        State.init_var_memory ();

        (* clause buffer has stabilized at this point, use direct reference from now on *)
        let clause_buf = Clauses.get_buffer () in

        Option.may (Clauses.dump_all clause_buf) (Opt.opt all_clauses_file);

        puts "Doing forward pass";
        forward_pass clause_buf;

        puts "Verifying proof backwards";
        set_verification_start_time ();
        verify_backward clause_buf;
        puts "Proof verified!";

        print_stats ();

        Option.may (State.dump_core clause_buf) (Opt.opt clause_core_file);
        Option.may (State.dump_proof clause_buf ~only_core:true ~only_core_deletions:(Opt.get only_core_deletions)) (Opt.opt lemma_core_file)
    | _ -> OptParser.usage opt_parser ()
  with
  | Trivially_unsat -> puts "Conflict in CNF, problem trivially UNSAT"