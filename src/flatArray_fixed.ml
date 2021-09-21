struct
  let uget = IntArray.unsafe_get
  let uset = IntArray.unsafe_set

  type t =
    { mutable size        : int (* current buffer size *)
    ; mutable top         : int (* next unused index in buffer *)
    ; mutable length      : int (* current number of elements *)
    ; mutable buffer      : int_array (* stores elements *) }

  let make_growing exp_n =
    dassert(exp_n*T.obj_size > 0);
    let new_array =
      { size = exp_n*T.obj_size
      ; top = 0
      ; length = 0
      ; buffer = IntArray.create (exp_n*T.obj_size) } in
    new_array

  let make_filled ~constructor n =
    dassert(n*T.obj_size > 0);
    let new_array =
      { size = n*T.obj_size
      ; top = n*T.obj_size
      ; length = n
      ; buffer = IntArray.create (n*T.obj_size) } in
    for i = 0 to (n-1) do
      constructor new_array.buffer (i*T.obj_size)
    done;
    new_array

  let empty () = make_growing 1

  let length a = a.length

  let realloc_size a new_s =
    dassert(new_s > a.size);
    a.size <- new_s;
    a.buffer <- IntArray.realloc a.buffer a.size

  let realloc a new_n =
    let new_s = new_n * T.obj_size in
    realloc_size a new_s

  let expand_buffer a =
    realloc_size a (expand_size a.size)

  let add_obj ~constructor a =
    while (a.top + T.obj_size) > a.size do
      expand_buffer a;
    done;

    let new_idx = a.length in
    let new_array_idx = {array_index = a.top} in
    a.top <- a.top + T.obj_size;
    a.length <- succ a.length;
    constructor a.buffer new_idx new_array_idx;
    new_array_idx

  let get a ai j =
    dassert(ai.array_index >= 0 && a.size > ai.array_index+j);
    uget a.buffer (ai.array_index+j)
  let set a ai j e =
    dassert(ai.array_index >= 0 && a.size > ai.array_index+j);
    uset a.buffer (ai.array_index+j) e

  let get_obj_array_index a i = array_indexify (T.obj_size*i)

  let get_last_obj_array_index a = get_obj_array_index a (a.length - 1)

  let get_next_array_index ai = array_indexify (ai.array_index+T.obj_size)

  let get_array_end a = get_obj_array_index a (a.length - 1)

  let remove_last a =
    dassert(a.length > 0);

    a.top <- a.top - T.obj_size;
    a.length <- pred a.length

  let iter_from f a si =
    let rec helper i =
      if i = a.length then () else begin
        f (get_obj_array_index a i);
        helper (succ i)
      end in
    dassert(0 <= si && si <= a.length);
    helper si

  let iter f a =
    iter_from f a 0

  let iter_backwards_from f a si =
    let rec helper i =
      if i = (-1) then () else begin
        f (get_obj_array_index a i);
        helper (pred i)
      end in
    dassert(0 <= si && si <= a.length);
    helper si

  let iter_backwards f a =
    iter_backwards_from f a (a.length - 1)
end