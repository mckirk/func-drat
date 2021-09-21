(*pp cppo *)

open Batteries
open Bigarray
open FlatArray

#include "debug.ml"

type literal = int
type literal_array_index = array_index

type trail_index = int
type trail_position = { trail_length : int }

type clause_index = int
type clause_array_index = array_index

type proof_step_index = int

module Literals = struct
  (* literals are usually encoded -x for negated x, which works for fast array access in C, but not in OCaml;
     therefore negating here becomes x lxor 1 and the encoding changes appropriately  *)
  let encode lit =
    if lit < 0
      then 2*(-lit)+1
      else 2*lit
  let decode lit =
    if (lit land 1) <> 0
      then -(lit lsr 1)
      else   lit lsr 1
  let negate lit = lit lxor 1
  let normalize lit = lit lsr 1 (* for sign-agnostic lookup *)
  let are_same a b = normalize a = normalize b

  let length = IntArray.length
  let empty ar = length ar = 0

  let cmp = Pervasives.compare
  let sort : int array -> unit = Array.sort cmp
  let inverse_cmp a b = ~-(cmp a b)
  let inverse_sort ls = Array.sort inverse_cmp ls

  let from_string_list lst =
    let rec no_tautologies = (function
      | l1 :: l2 :: rest ->
        if l1 = negate l2 then false
        else no_tautologies (l2 :: rest)
      | _ -> true) in

    let sorted_lits = List.sort_unique cmp @@ List.map (encode % String.to_int) lst in
    assert (List.hd sorted_lits = 0);
    assert (no_tautologies sorted_lits);
    Array.of_list @@ List.tl sorted_lits
  let from_string str = from_string_list @@ Str.split Misc.whitespace_regex str

  let to_str lits =
    String.concat " " @@ List.map (String.of_int % decode) @@ (flip List.append [0]) @@ IntArray.to_list lits

  let invalid_lit = -1
end

module WatchListEntryDef = struct
  let obj_size = 5
end

module ClauseDef = struct
  let clause_vars_size = 4
  let fixed_part_size = clause_vars_size + (2*WatchListEntryDef.obj_size)
end

module ProofStepDef = struct
  let obj_size = 3
end

(* use "ghetto-functors" for better performance *)

module ClauseArray =
#define T ClauseDef
#include "flatArray_variable.ml"
#undef T

module ProofStepArray =
#define T ProofStepDef
#include "flatArray_fixed.ml"
#undef T

type clause_array = ClauseArray.t
type proof_step_array = ProofStepArray.t

let storage_clauses = ClauseArray.empty ()
let storage_proof_steps = ProofStepArray.empty ()

module Trail = struct
  let invalid_position = {trail_length = -1}
end

(* watchlist entries also live on the clause array *)
module WatchListEntry = struct
  let end_of_list = array_indexify (-1)

  let is_eol entry = entry.array_index < 0

  let get_clause buf entry = array_indexify @@ IntArray.get_elem buf entry 0
  let set_clause buf entry ai = IntArray.set_elem buf entry 0 ai.array_index

  let get_literal buf entry = IntArray.get_elem buf entry 1
  let set_literal buf entry lit = IntArray.set_elem buf entry 1 lit

  let get_backward buf entry = array_indexify @@ IntArray.get_elem buf entry 2
  let set_backward buf entry ai = IntArray.set_elem buf entry 2 ai.array_index

  let get_forward buf entry = array_indexify @@ IntArray.get_elem buf entry 3
  let set_forward buf entry ai = IntArray.set_elem buf entry 3 ai.array_index

  let get_lit_position buf entry = IntArray.get_elem buf entry 4
  let set_lit_position buf entry pos = IntArray.set_elem buf entry 4 pos

  let constructor buf clause pos entry =
    set_clause buf entry clause;
    set_lit_position buf entry pos;
    set_literal buf entry Literals.invalid_lit;
    set_backward buf entry end_of_list;
    set_forward buf entry end_of_list
end

module Clause = struct
  open ClauseDef

  let no_reason = array_indexify (-1)
  let invalid = array_indexify (-1)

  let set_flag = (lor)
  let unset_flag = (land) % lnot
  let bool_to_flag flag b = if b then set_flag flag else unset_flag flag
  let has_flag flag = ((<>) 0) % (land) flag

  let core_flag = 1 (* clause lead to conflict at some point and therefore played role in verification *)
  let const_unit_flag = 2 (* clause was unit already at initialization, therefore has no watches *)
  let deleted_flag = 4 (* clause has been 'deleted' already *)

  let is_core buf clause        = has_flag core_flag @@ IntArray.get_elem buf clause 0
  let is_const_unit buf clause  = has_flag const_unit_flag @@ IntArray.get_elem buf clause 0
  let is_deleted buf clause     = has_flag deleted_flag @@ IntArray.get_elem buf clause 0

  let set_is_core buf clause        = IntArray.mod_elem buf clause 0 % bool_to_flag core_flag
  let set_is_const_unit buf clause  = IntArray.mod_elem buf clause 0 % bool_to_flag const_unit_flag
  let set_is_deleted buf clause     = IntArray.mod_elem buf clause 0 % bool_to_flag deleted_flag

  let get_trail_before_used buf clause = {trail_length = IntArray.get_elem buf clause 1}
  let set_trail_before_used buf clause position = IntArray.set_elem buf clause 1 position.trail_length

  let get_length buf clause = IntArray.get_elem buf clause 2
  let set_length buf clause = IntArray.set_elem buf clause 2

  let get_index buf clause = IntArray.get_elem buf clause 3
  let set_index buf clause = IntArray.set_elem buf clause 3

  let get_watchlist_entry clause i =
    dassert(0 <= i && i <= 1);
    array_indexify @@ clause.array_index + clause_vars_size + (i*WatchListEntryDef.obj_size)

  let get_literal buf clause i = IntArray.get_elem buf clause (fixed_part_size+i)
  let set_literal buf clause i = IntArray.set_elem buf clause (fixed_part_size+i)
  let get_literals buf clause = IntArray.sub_elems buf clause ~start:fixed_part_size ~len:(get_length buf clause)

  let constructor new_lits buf clause_idx clause =
    let lit_count = IntArray.length new_lits in
    assert (lit_count > 0);
    set_is_core buf clause false;
    set_is_const_unit buf clause false;
    set_is_deleted buf clause false;
    set_trail_before_used buf clause Trail.invalid_position;
    set_length buf clause lit_count;
    set_index buf clause clause_idx;

    WatchListEntry.constructor buf clause 0 (get_watchlist_entry clause 0);
    WatchListEntry.constructor buf clause 1 (get_watchlist_entry clause 1);

    IntArray.blit new_lits (get_literals buf clause)

  let to_str buf clause = Literals.to_str (get_literals buf clause)

  let get_literal_list buf clause = List.init (get_length buf clause) (get_literal buf clause)
  let swap_literals buf clause i1 i2 = IntArray.swap_elems buf clause (fixed_part_size+i1) (fixed_part_size+i2)

  let find_literal_index buf clause p ~start =
    IntArray.findi_elem buf clause p ~offset:fixed_part_size ~start ~len:(get_length buf clause - start)
  let find_literal_index2 buf clause p ~start =
    IntArray.findi_elem2 buf clause p ~offset:fixed_part_size ~start ~len:(get_length buf clause - start)

  let iter_literals buf clause f =
    IntArray.iter_elems f buf clause ~start:(fixed_part_size) ~len:(get_length buf clause)

  let has_literal buf clause lit =
    IntArray.has_elem buf clause lit ~start:(fixed_part_size) ~len:(get_length buf clause)

  let get_ID buf clause = if clause = no_reason then (-1) else (get_index buf clause) + 1
  let to_pretty_str buf clause = Printf.sprintf "[%d]: %s" (get_ID buf clause) (to_str buf clause)
end

module Clauses = struct
  let add new_lits =
    let lit_count = IntArray.length new_lits in
    ClauseArray.add_obj storage_clauses ~var_size:lit_count ~constructor:(Clause.constructor new_lits)

  let get_buffer () = ClauseArray.get_buffer storage_clauses

  let clause_by_index idx = ClauseArray.get_obj_array_index storage_clauses idx

  let dump_all buf file =
    File.with_file_out file
      (fun h -> ClauseArray.iter_indices
        (fun c -> IO.nwrite h (Clause.to_str buf c ^ "\n")) storage_clauses)
end



type proof_step =
    LemmaIndex of clause_array_index * literal (* stores pivot literal as well *)
  | DeletionIndex of clause_array_index
  | ConflictClause

module ProofSteps = struct
  let get ps_ai =
    match ProofStepArray.get storage_proof_steps ps_ai 0 with
    | 0 -> LemmaIndex (array_indexify @@ ProofStepArray.get storage_proof_steps ps_ai 1, (ProofStepArray.get storage_proof_steps ps_ai 2))
    | 1 -> DeletionIndex (array_indexify @@ ProofStepArray.get storage_proof_steps ps_ai 1)
    | 2 -> ConflictClause
    | _ -> failwith "Invalid proof_step encoding encountered"

  let constructor proof_step _ _ ps_ai =
    match proof_step with
    | LemmaIndex (clause, lit) ->
        ProofStepArray.set storage_proof_steps ps_ai 0 0;
        ProofStepArray.set storage_proof_steps ps_ai 1 clause.array_index;
        ProofStepArray.set storage_proof_steps ps_ai 2 lit
    | DeletionIndex clause ->
        ProofStepArray.set storage_proof_steps ps_ai 0 1;
        ProofStepArray.set storage_proof_steps ps_ai 1 clause.array_index
    | ConflictClause ->
        ProofStepArray.set storage_proof_steps ps_ai 0 2

  let get_all () = storage_proof_steps
  let add proof_step = ProofStepArray.add_obj storage_proof_steps ~constructor:(constructor proof_step)

  let get_length () = ProofStepArray.length storage_proof_steps

  let step_by_index idx = get (ProofStepArray.get_obj_array_index storage_proof_steps idx)

  let iter f = ProofStepArray.iter f storage_proof_steps
  let iter_backwards_from f i = ProofStepArray.iter_backwards_from f storage_proof_steps i
end

exception Error_wrong_input_syntax
exception Error_inconsistent_assignment of literal
exception Error_unit_literal_unassigned of literal
exception Error_invalid_proof of string
exception Error_lemma_not_redundant of clause_array_index

exception Trivially_unsat
exception Clause_already_falsified
exception Found_conflict of clause_array_index
exception Found_conflict_step of proof_step_index
exception Blocked_clause of literal

type clause_selection = Core | Non_core