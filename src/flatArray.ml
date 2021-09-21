(*pp cppo *)

open Batteries
open Bigarray

#include "debug.ml"

type array_index = { array_index : int } [@@unboxed]
let array_indexify ai = {array_index = ai}

type int_array = (int, int_elt, c_layout) Array1.t

let expand_size s = 2*s

module IntArray = struct
  module A = Array1

  let create = A.create int c_layout
  let create_filled n e =
    let new_array = create n in
    A.fill new_array e;
    new_array

  let empty () = create 0

  let length : int_array -> int = A.dim

  let of_array = A.of_array int c_layout

  let sub : int_array -> int -> int -> int_array = A.sub
  let blit : int_array -> int_array -> unit = A.blit
  let get : int_array -> int -> int = A.get
  let set : int_array -> int -> int -> unit = A.set

  let unsafe_get : int_array -> int -> int = A.unsafe_get
  let uget = unsafe_get
  let unsafe_set : int_array -> int -> int -> unit = A.unsafe_set
  let uset = unsafe_set

  let realloc ar new_size =
    let old_size = length ar in
    dassert(new_size > old_size);
    let new_array = create new_size in
    A.blit ar (A.sub new_array 0 old_size);
    new_array

  let realloc_filled ar new_size e =
    let old_size = length ar in
    dassert(new_size > old_size);
    let new_array = create new_size in
    A.blit ar (A.sub new_array 0 old_size);
    A.fill (A.sub new_array old_size (new_size-old_size)) e;
    new_array


  let fold f start ar =
    let rec fold i x =
      if i = length ar
      then x
      else fold (succ i) (f x @@ uget ar i) in
    fold 0 start

  let iter f ar =
    for i = 0 to length ar - 1 do
      f @@ uget ar i
    done

  let iter_backwards f ar =
    for i = length ar - 1 downto 0 do
      f @@ uget ar i
    done

  let contains ar e ?(start=0) ~len =
    let rec helper i l =
      if l = 0
      then false
      else uget ar i = e || helper (succ i) (pred l) in
    helper start len

  let to_list ar = List.init (length ar) (fun i -> uget ar i)

  let of_list l =
    let new_array = create (List.length l) in
    let rec list_blit i = function
    | x :: rest -> uset new_array i x; list_blit (succ i) rest
    | [] -> () in
    list_blit 0 l;
    new_array

  let swap ar f t =
    dassert(min f t >= 0 && length ar > max f t);
    let temp = uget ar f in
    uset ar f @@ uget ar t;
    uset ar t temp

  let rec findi ar p ~offset ?(start=0) ~len =
    if len = 0 then None
    else
      let e = uget ar (offset+start) in
      if p e
        then Some (start, e)
        else findi ar ~offset:offset ~start:(succ start) ~len:(pred len) p

  let rec findi2 ar p ~offset ?(start=0) ~len =
    if len = 0 then (None, None)
    else
      let e = uget ar (offset+start) in
      if p e
        then (Some (start, e), findi ar ~offset:offset ~start:(succ start) ~len:(pred len) p)
        else findi2 ar ~offset:offset ~start:(succ start) ~len:(pred len) p

  let get_elem ar ai j =
    dassert(ai.array_index >= 0 && length ar > ai.array_index + j);
    uget ar (ai.array_index+j)

  let set_elem ar ai j e =
    dassert(ai.array_index >= 0 && length ar > ai.array_index + j);
    uset ar (ai.array_index+j) e

  let mod_elem ar ai j f =
    dassert(ai.array_index >= 0 && length ar > ai.array_index + j);
    set_elem ar ai j @@ f @@ get_elem ar ai j

  let sub_elems ar ai ~start ~len =
    dassert(ai.array_index >= 0 && length ar > ai.array_index + start + len);
    sub ar (ai.array_index+start) len

  let swap_elems ar ai j1 j2 =
    swap ar (ai.array_index+j1) (ai.array_index+j2)

  let findi_elem ar ai p ~offset ?(start=0) ~len =
    findi ar p ~offset:(ai.array_index+offset) ~start ~len

  let findi_elem2 ar ai p ~offset ?(start=0) ~len =
    findi2 ar p ~offset:(ai.array_index+offset) ~start ~len

  let iter_elems f ar ai ~start ~len =
    for i = ai.array_index+start to ai.array_index+start + len - 1 do
      f (uget ar i)
    done

  let has_elem ar ai e ~start ~len =
    contains ar e ~start:(ai.array_index+start) ~len
end

module type VariableSizeType = sig
  val fixed_part_size : int
end

module type FixedSizeType = sig
  val obj_size : int
end