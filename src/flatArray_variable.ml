struct
  let uget = IntArray.uget
  let uset = IntArray.uset

  type t =
    { mutable size        : int (* current buffer size *)
    ; mutable top         : int (* next unused index in buffer *)
    ; mutable lookup_size : int
    ; mutable length      : int (* current number of elements *)
    ; mutable buffer      : int_array (* stores elements *)
    ; mutable lookup      : int_array (* element-index to buffer-index table *)}

  let make exp_n exp_s =
    dassert(exp_n * exp_s > 0);
    let new_array =
      { size = exp_n*exp_s
      ; top = 0
      ; lookup_size = exp_n
      ; length = 0
      ; buffer = IntArray.create (exp_n*exp_s)
      ; lookup = IntArray.create exp_n } in
    new_array

  let empty () = make 1 1 (* allocate at least one element *)

  let length a = a.length

  let get_buffer a = a.buffer

  let realloc a n s =
    let new_size = n*s in
    dassert(new_size >= a.size && n >= a.lookup_size);
    a.size <- new_size;
    a.lookup_size <- n;
    a.buffer <- IntArray.realloc a.buffer a.size;
    a.lookup <- IntArray.realloc a.lookup a.lookup_size

  let expand_buffer a =
    a.size <- expand_size a.size;
    a.buffer <- IntArray.realloc a.buffer a.size

  let expand_lookup a =
    a.lookup_size <- expand_size a.lookup_size;
    a.lookup <- IntArray.realloc a.lookup a.lookup_size

  let add_obj ~constructor ~var_size a =
    let size = T.fixed_part_size + var_size in
    while (a.top + size) > a.size do
      expand_buffer a;
    done;
    if a.length = a.lookup_size then
      expand_lookup a;

    let new_idx = a.length in
    let new_array_idx = {array_index = a.top} in
    uset a.lookup new_idx a.top;
    constructor a.buffer new_idx new_array_idx;
    a.top <- a.top + size;
    a.length <- succ a.length;
    new_array_idx

  (* append an element to the variable-sized object-tail *)
  let extend_obj_tail a e =
    if a.top = a.size then
      expand_buffer a;

    uset a.buffer (a.top) e;
    a.top <- succ a.top

  (* return an indexed element from an object *)
  let get a ai j =
    dassert(ai.array_index >= 0 && a.size > ai.array_index+j);
    uget a.buffer (ai.array_index+j)

  let set a ai j e =
    dassert(ai.array_index  >= 0 && a.size > ai.array_index+j);
    uset a.buffer (ai.array_index+j) e

  let get_var_slice a ai l = IntArray.sub a.buffer (ai.array_index+T.fixed_part_size) l

  let get_var_elem a ai j = get a ai (T.fixed_part_size+j)
  let set_var_elem a ai j = set a ai (T.fixed_part_size+j)

  let swap_var_elems a ai i j = IntArray.swap a.buffer (ai.array_index+T.fixed_part_size+i) (ai.array_index+T.fixed_part_size+j)

  let find_var_elem  a ai p ~start ~len = IntArray.findi  a.buffer p ~offset:(ai.array_index+T.fixed_part_size) ~start:start ~len:len
  let find_var_elem2 a ai p ~start ~len = IntArray.findi2 a.buffer p ~offset:(ai.array_index+T.fixed_part_size) ~start:start ~len:len

  let has_var_elem a ai e ~len = IntArray.contains a.buffer e ~start:(ai.array_index+T.fixed_part_size) ~len:len

  let iter_var_elems f a ai ~len =
    for i = ai.array_index+T.fixed_part_size to ai.array_index+T.fixed_part_size + len - 1 do
      f (uget a.buffer i)
    done

  let get_obj_array_index a i =
    dassert(i >= 0 && a.length > i);
    let array_index = uget a.lookup i in
    {array_index}

  let get_last_obj_array_index a = get_obj_array_index a (a.length - 1)

  let remove_last a =
    dassert(a.length > 0);
    let last_idx = a.length - 1 in

    a.top <- uget a.lookup last_idx;
    uset a.lookup last_idx (-1);
    a.length <- pred a.length

  let iter_indices f a =
    for i = 0 to a.length - 1 do
      f (get_obj_array_index a i)
    done
end