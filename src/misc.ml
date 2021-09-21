open Batteries

let whitespace_regex = Str.regexp "[ \n\t]+"

(* interesting things are possible with ref-types... mapping over Enums with an accumulator for example *)
let rec enum_acc_map f enum init =
  let acc = ref init in
  Enum.make
    ~next:(fun () -> let (r, nacc) = f (Enum.get_exn enum) !acc in acc := nacc; r)
    ~count:(fun () -> Enum.count enum)
    ~clone:(fun () -> enum_acc_map f (Enum.clone enum) !acc)

let update_array_elem a ~i ~f = Array.set a i (f @@ Array.get a i)
let swap_array_elems a i j = let t = a.(i) in a.(i) <- a.(j); a.(j) <- t
let rec findi_array a ?(start=0) f =
  if start = Array.length a then None
  else if f a.(start) then Some start else findi_array a ~start:(succ start) f
let rec findi_array2 a ?(start=0) f =
  if start = Array.length a then (None, None)
  else if f a.(start) then (Some start, findi_array a ~start:(succ start) f) else findi_array2 a ~start:(succ start) f