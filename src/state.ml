(*pp cppo *)

open Batteries
open Printf
open Types
open FlatArray

#include "debug.ml"

let hashsize = 1000000
let avg_clause_length = 10

type checker_state =
  { mutable max_vars        : int
  ; mutable max_clauses     : int
  ; mutable num_vars        : int
  ; mutable num_total_clauses : int
  ; mutable num_clauses     : int
  ; mutable num_lemmas      : int
  ; mutable num_core_clauses: int
  ; mutable num_core_lemmas : int
  ; mutable start_lemmas    : clause_index
  ; mutable first_lemma     : clause_array_index
  ; mutable hash_table      : clause_index list array

  (* contains inverted assignments and markings; if entry <> 0 -> literal false *)
  ; mutable assignment      : int_array

  ; mutable trail           : int_array
  ; mutable falsification_reason : int_array
  ; mutable lits_assigned   : trail_index
  ; mutable lits_processed_noncore : trail_index
  ; mutable lits_processed_core : trail_index

  ; mutable watchlist_starts_noncore : int_array
  ; mutable watchlist_starts_core : int_array

  ; mutable conflict_step   : int }

let state =
  { max_vars        = 0
  ; max_clauses     = 0
  ; num_vars        = 0
  ; num_total_clauses = 0
  ; num_clauses     = 0
  ; num_lemmas      = 0
  ; num_core_clauses= 0
  ; num_core_lemmas = 0
  ; start_lemmas    = 0
  ; first_lemma     = Clause.invalid
  ; hash_table      = Array.init hashsize (const [])
  ; assignment      = IntArray.empty ()
  ; trail           = IntArray.empty ()
  ; falsification_reason = IntArray.empty ()
  ; lits_assigned   = 0
  ; lits_processed_noncore = 0
  ; lits_processed_core = 0
  ; watchlist_starts_noncore = IntArray.empty ()
  ; watchlist_starts_core = IntArray.empty ()
  ; conflict_step   = 0 }

module LitAssignment = struct
  let is_false = 1
  let temp_assignment = 2
  let marked_for_core = 3
  let reason_in_core = 4
end

let get_lit_at_trail_pos pos = IntArray.uget state.trail pos
let set_lit_at_trail_pos pos lit = IntArray.uset state.trail pos lit

let get_assignment lit = IntArray.uget state.assignment lit
let set_assignment lit assignment = IntArray.uset state.assignment lit assignment

let get_falsification_reason lit = array_indexify @@ IntArray.uget state.falsification_reason lit
let set_falsification_reason lit clause = IntArray.uset state.falsification_reason lit clause.array_index

let set_conflict_step i = state.conflict_step <- i
let iter_steps_backwards_from_conflict f = ProofSteps.iter_backwards_from f state.conflict_step

let watchlist_array ~core = if core then state.watchlist_starts_core else state.watchlist_starts_noncore
let get_watchlist_start ~core lit = array_indexify @@ IntArray.uget (watchlist_array ~core) lit
let set_watchlist_start ~core lit entry = IntArray.uset (watchlist_array ~core) lit entry.array_index

let get_clause_stats () = (state.num_clauses, state.num_core_clauses)
let get_lemma_stats () = (state.num_lemmas, state.num_core_lemmas)

let set_problem_dimensions n_vars n_clauses =
  state.max_vars     <- n_vars;
  state.max_clauses  <- n_clauses;
  printf "Num clauses %d, num variables %d\n" state.max_clauses state.max_vars

let init_clause_memory () =
  ClauseArray.realloc storage_clauses state.max_clauses (ClauseDef.fixed_part_size + avg_clause_length)

let init_var_memory () =
  let num_slots = 2*state.max_vars + 2 in

  state.trail         <- IntArray.create_filled (state.max_vars+1) (Literals.invalid_lit);
  state.assignment    <- IntArray.create_filled num_slots 0;
  state.falsification_reason <- IntArray.create_filled num_slots Clause.no_reason.array_index;
  state.watchlist_starts_noncore <- IntArray.create_filled num_slots WatchListEntry.end_of_list.array_index;
  state.watchlist_starts_core <- IntArray.create_filled num_slots WatchListEntry.end_of_list.array_index

let switch_to_lemmas () = (* clauses finished, next come the lemmas *)
  dassert(state.num_clauses = state.max_clauses);
  state.start_lemmas <- state.num_clauses


let ghetto_hash ls = (* fell from the sky in drat-trim*)
  let f (s, p, x) lit = (s + lit, p * lit, x lxor lit) in
  let sum, prod, xor = IntArray.fold f (0, 1, 0) ls in
  abs (1023 * sum + prod lxor (31 * xor)) mod hashsize

let insert_hash clause literals =
  Misc.update_array_elem state.hash_table ~i:(ghetto_hash literals) ~f:(List.cons clause.array_index)
let remove_hash clause literals =
  Misc.update_array_elem state.hash_table ~i:(ghetto_hash literals) ~f:(flip List.remove clause.array_index)
let find_and_remove_hashed_clause literals =
  let find_by_lits clause_ai =
    Clause.get_literals (Clauses.get_buffer ()) (array_indexify clause_ai) = literals in

  let hash = ghetto_hash literals in
  let found_ai = List.find find_by_lits state.hash_table.(hash) in
  Misc.update_array_elem state.hash_table ~i:hash ~f:(flip List.remove found_ai);
  array_indexify found_ai

let get_trail_position () = {trail_length = state.lits_assigned}
let backtrack_to_trail_position clause_buf position =
  dassert(position.trail_length >= 0 && position.trail_length <= state.lits_assigned);
  while state.lits_assigned > position.trail_length do
    dassert(state.lits_assigned > 0);
    let last_trail_pos = pred state.lits_assigned in

    let lit = get_lit_at_trail_pos last_trail_pos in
    dprintf("Unassigning literal %d\n" (Literals.decode lit));

    dassert(get_assignment (Literals.negate lit) = 0);
    (* trail entry and assign reason do not need to be cleared, because they are assumed to be
       valid only when the variable is assigned *)
    set_assignment lit 0;
    state.lits_assigned <- last_trail_pos;
  done;

  state.lits_processed_noncore <- min state.lits_assigned state.lits_processed_noncore;
  state.lits_processed_core <- min state.lits_assigned state.lits_processed_core

let dump_trail () =
  dprintf("Current assignment trail, size %d: " state.lits_assigned);
  for i = 0 to state.lits_assigned - 1 do
    dprintf("%d " (Literals.decode @@ get_lit_at_trail_pos i))
  done;
  dprintf("\n")

let iter_unprocessed_literals f selector =
  let rec iter_lits_from n =
    if n >= state.lits_assigned then ()
    else begin
      f (get_lit_at_trail_pos n);
      iter_lits_from (succ n)
    end in
  match selector with
  | Core ->
      iter_lits_from state.lits_processed_core;
      state.lits_processed_core <- state.lits_assigned
  | Non_core ->
      iter_lits_from state.lits_processed_noncore;
      state.lits_processed_noncore <- state.lits_assigned

(* invariant: assignments/trail/etc are the same before and after *)
let sandbox_assignment_effects clause_buf f =
  let position = get_trail_position () in
  try
    let result = f () in
    backtrack_to_trail_position clause_buf position;
    result
  with ex ->
    printf "Got exception while in assignment sandbox, state inconsistent!\n";
    raise ex

let unfalsified     lit = get_assignment lit = 0
let assigned_false  lit = get_assignment lit <> 0
let assigned_true   lit = assigned_false (Literals.negate lit)

let assign_false clause_buf lit responsible_clause =
  let trail_pos = state.lits_assigned in
  dprintf("Assigning false to literal %d because of clause %d\n" (Literals.decode lit) (Clause.get_ID clause_buf responsible_clause));
  dassert(not @@ (assigned_true lit || assigned_false lit));

  if responsible_clause <> Clause.no_reason then
    set_assignment lit LitAssignment.is_false
  else
    set_assignment lit LitAssignment.temp_assignment;

  set_lit_at_trail_pos trail_pos lit;
  set_falsification_reason lit responsible_clause;

  state.lits_assigned <- succ trail_pos;
#ifdef DEBUG
  dump_trail ()
#else
  ()
#endif

let assign_true clause_buf lit responsible_clause =
  assign_false clause_buf (Literals.negate lit) responsible_clause

let get_watchlist_lit clause_buf watchlist_entry =
  let start_lit = WatchListEntry.get_literal clause_buf watchlist_entry in
  let is_core = Clause.is_core clause_buf @@ WatchListEntry.get_clause clause_buf watchlist_entry in
  let rec helper wle =
    let lit = WatchListEntry.get_literal clause_buf wle in
    dassert(lit <> Literals.invalid_lit);
    let prev_wle = WatchListEntry.get_backward clause_buf wle in
    dassert(lit = start_lit);
    if WatchListEntry.is_eol prev_wle then begin
      dassert(get_watchlist_start ~core:is_core lit = wle);
      lit
    end else
      helper prev_wle in
  helper watchlist_entry

let dump_watchlist clause_buf watchlist_entry =
  let lit = get_watchlist_lit clause_buf watchlist_entry in
  let start_clause = WatchListEntry.get_clause clause_buf watchlist_entry in
  let rec helper_back wle str =
    if WatchListEntry.is_eol wle then str
    else begin
      let clause = WatchListEntry.get_clause clause_buf wle in
      helper_back (WatchListEntry.get_backward clause_buf wle) (sprintf "clause %d - %s" (Clause.get_ID clause_buf clause) str)
    end in
  let rec helper_fwd wle str =
    if WatchListEntry.is_eol wle then str
    else begin
      let clause = WatchListEntry.get_clause clause_buf wle in
      helper_fwd (WatchListEntry.get_forward clause_buf wle) (sprintf "%s - clause %d" str (Clause.get_ID clause_buf clause))
    end in
  let str =
    helper_fwd (WatchListEntry.get_forward clause_buf watchlist_entry) @@
    helper_back (WatchListEntry.get_backward clause_buf watchlist_entry) @@
    sprintf ">clause %d<" (Clause.get_ID clause_buf start_clause) in
  printf "lit %d - %s\n%!" (Literals.decode lit) str

let add_watch clause_buf (pos, lit) clause =
  let clause_wle = Clause.get_watchlist_entry clause pos in
  let is_core = Clause.is_core clause_buf clause in
  let wl_start = get_watchlist_start ~core:is_core lit in

  dassert(WatchListEntry.get_literal clause_buf clause_wle = Literals.invalid_lit);

  WatchListEntry.set_literal clause_buf clause_wle lit;

  if not @@ WatchListEntry.is_eol wl_start then
    WatchListEntry.set_backward clause_buf wl_start clause_wle;

  WatchListEntry.set_backward clause_buf clause_wle WatchListEntry.end_of_list;
  WatchListEntry.set_forward clause_buf clause_wle wl_start;

  set_watchlist_start ~core:is_core lit clause_wle

let remove_watch clause_buf (pos, lit) clause =
  let clause_wle = Clause.get_watchlist_entry clause pos in
  let prev_wle = WatchListEntry.get_backward clause_buf clause_wle in
  let next_wle = WatchListEntry.get_forward clause_buf clause_wle in
  let is_core = Clause.is_core clause_buf clause in

  dassert(WatchListEntry.get_literal clause_buf clause_wle <> Literals.invalid_lit);

  if WatchListEntry.is_eol prev_wle then begin
    dassert(get_watchlist_start ~core:is_core lit = clause_wle);
    set_watchlist_start ~core:is_core lit next_wle
  end else begin
    dassert(get_watchlist_lit clause_buf clause_wle = lit);
    WatchListEntry.set_forward clause_buf prev_wle next_wle
  end;

  if not @@ WatchListEntry.is_eol next_wle then
    WatchListEntry.set_backward clause_buf next_wle prev_wle;

  WatchListEntry.set_literal clause_buf clause_wle Literals.invalid_lit

let iter_watch_clauses clause_buf sel f lit =
  let rec helper wle =
    if WatchListEntry.is_eol wle then ()
    else begin
      let next_wle = WatchListEntry.get_forward clause_buf wle in
      let clause = WatchListEntry.get_clause clause_buf wle in
      let lit_pos = WatchListEntry.get_lit_position clause_buf wle in
      f clause lit_pos;
      helper next_wle
    end in
  helper @@ get_watchlist_start ~core:(sel = Core) lit

let move_watch clause_buf clause ((from_pos, from_lit) as from) (to_pos, to_lit) =
  dprintf("Moving watch from literal %d to %d in clause %d\n"
    (Literals.decode from_lit) (Literals.decode to_lit) (Clause.get_ID clause_buf clause));
  remove_watch clause_buf from clause;
  Clause.set_literal clause_buf clause from_pos to_lit;
  Clause.set_literal clause_buf clause to_pos from_lit;
  add_watch clause_buf (from_pos, to_lit) clause

let reference_clause clause_buf clause =
  if Clause.is_deleted clause_buf clause &&
      not (Clause.is_const_unit clause_buf clause) &&
      Clause.get_length clause_buf clause >= 2 then begin
    add_watch clause_buf (0, (Clause.get_literal clause_buf clause 0)) clause;
    add_watch clause_buf (1, (Clause.get_literal clause_buf clause 1)) clause;
  end;
  Clause.set_is_deleted clause_buf clause false
let unreference_clause clause_buf clause =
  if not (Clause.is_deleted clause_buf clause) &&
      not (Clause.is_const_unit clause_buf clause) &&
      Clause.get_length clause_buf clause >= 2 then begin
    remove_watch clause_buf (0, (Clause.get_literal clause_buf clause 0)) clause;
    remove_watch clause_buf (1, (Clause.get_literal clause_buf clause 1)) clause;
  end;
  Clause.set_is_deleted clause_buf clause true

let move_clause_to_core clause_buf clause =
  if not (Clause.is_core clause_buf clause) then begin
    if clause.array_index >= state.first_lemma.array_index
      then state.num_core_lemmas <- succ state.num_core_lemmas
      else state.num_core_clauses <- succ state.num_core_clauses;

    let is_deleted = Clause.is_deleted clause_buf clause in
    if not is_deleted then unreference_clause clause_buf clause;
    Clause.set_is_core clause_buf clause true;
    if not is_deleted then reference_clause clause_buf clause
  end

let mark_as_core clause_buf conflict_clause =
  let get_unmarked_literals clause ~start_list =
    let len = Clause.get_length clause_buf clause in
    let rec loop l i =
      if i = len then l
      else
        let lit = Clause.get_literal clause_buf clause i in
        let old_assignment = get_assignment lit in
        (* if lit isn't marked or temporary or in core yet *)
        if old_assignment = LitAssignment.is_false then begin
          set_assignment lit LitAssignment.marked_for_core;
          loop (lit :: l) (succ i)
        end else
          loop l (succ i) in
    loop start_list 0 in

  let rec mark_reasons = (function
  | lit :: rest ->
      let reason = get_falsification_reason lit in
      dassert(assigned_false lit || assigned_true lit);
      dassert(reason <> Clause.no_reason);
      dprintf("Marking reason %d for literal %d as core\n" (Clause.get_ID clause_buf reason) (Literals.decode lit));
      set_assignment lit LitAssignment.reason_in_core;
      move_clause_to_core clause_buf reason;
      mark_reasons (get_unmarked_literals reason rest)
  | [] -> ()) in

  dprintf("Marking conflict-clause %d as core\n" (Clause.get_ID clause_buf conflict_clause));
  move_clause_to_core clause_buf conflict_clause;
  mark_reasons (get_unmarked_literals conflict_clause [])

let iter_clauses_only f = (* iterates _only_ over clauses, not lemmas *)
  for i = 0 to state.start_lemmas - 1 do
    f @@ Clauses.clause_by_index i;
  done

let get_rat_candidates clause_buf neg_lit =
  let rec helper i cs =
    if i = state.num_total_clauses then cs
    else begin
      let clause = Clauses.clause_by_index i in
      if WatchListEntry.get_literal clause_buf (Clause.get_watchlist_entry clause 0) <> Literals.invalid_lit &&
        Clause.has_literal clause_buf clause neg_lit
      then helper (succ i) (clause :: cs)
      else helper (succ i) cs
    end in
  helper 0 []

let add_clause literals = (* takes sorted literals in boxed array form *)
  let intarray_lits = IntArray.of_array literals in
  let lit_count = Array.length literals in
  let new_clause = Clauses.add intarray_lits in

  let max_lit = IntArray.uget intarray_lits (lit_count - 1) in
  state.max_vars <- max state.max_vars (Literals.normalize max_lit);

  insert_hash new_clause intarray_lits;

  state.num_total_clauses <- succ state.num_total_clauses;

  if state.start_lemmas <> 0 then begin
    if state.first_lemma = Clause.invalid then
      state.first_lemma <- new_clause;
    state.num_lemmas <- succ state.num_lemmas
  end else
    state.num_clauses <- succ state.num_clauses;

  new_clause

let get_conflict_trace clause_buf clause =
  let rec collect_reasons = (function
  | lit :: rest ->
      dassert(assigned_true lit || assigned_false lit);
      let reason = get_falsification_reason lit in
      if reason <> Clause.no_reason then
        let reason_lits = Clause.get_literal_list clause_buf reason in
        (Clause.get_ID clause_buf reason) :: collect_reasons (reason_lits @ rest)
      else
        collect_reasons rest
  | [] -> []) in

  List.unique_cmp @@ (Clause.get_ID clause_buf clause) :: (collect_reasons @@ Clause.get_literal_list clause_buf clause)

let dump_core clause_buf file =
  let num_core_clauses = ref 0 in

  iter_clauses_only (fun clause ->
    if Clause.is_core clause_buf clause then num_core_clauses := succ !num_core_clauses);

  File.with_file_out file
    (fun h ->
      fprintf h "p cnf %d %d\n" state.max_vars !num_core_clauses;
      iter_clauses_only (fun clause ->
        if Clause.is_core clause_buf clause then IO.nwrite h (Clause.to_str clause_buf clause ^ "\n")))

let dump_proof clause_buf ~only_core ~only_core_deletions file =
  let ps_to_str = (function
  | LemmaIndex (clause, lit) ->
      let lit_list = Clause.get_literal_list clause_buf clause in
      let pivot_list = List.unique_cmp @@ ([lit] @ lit_list @ [0]) in
      if (not only_core) || (Clause.is_core clause_buf clause) then
        Some (String.concat " " @@ List.map (String.of_int % Literals.decode) pivot_list)
      else
        None
  | DeletionIndex clause ->
      if (not (Clause.is_const_unit clause_buf clause)) && ((not only_core_deletions) || Clause.is_core clause_buf clause) then
        Some ("d " ^ Clause.to_str clause_buf clause)
      else
        None
  | ConflictClause -> Some "0") in

  File.with_file_out file
    (fun h -> ProofSteps.iter
      (fun ps_ai ->
        match ps_to_str (ProofSteps.get ps_ai) with Some str -> IO.nwrite h (str ^ "\n") | _ -> ()))