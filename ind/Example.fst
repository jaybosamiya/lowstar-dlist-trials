module Example

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module DLL = DoublyLinkedListIface
module L = FStar.List.Tot

open DLL

let rec l_reverse (l:list 'a) : GTot (list 'a) =
  match l with
  | [] -> []
  | hd :: tl ->
    L.snoc ((l_reverse tl), hd)

let rec reverse (d:dll 'a) :
  HST.Stack (unit)
    (fun h0 -> dll_valid h0 d)
    (fun h0 () h1 ->
       dll_valid h1 d /\
       as_list h1 d == l_reverse (as_list h0 d) /\
       B.modifies (fp_dll h0 d) h0 h1 /\
       fp_dll h0 d `loc_equiv` fp_dll h1 d) =
  HST.push_frame ();
  if is_empty d then (
    ()
  ) else (
    let n = dll_head d in
    dll_remove_head d;
    reverse d;
    dll_insert_at_tail d n
  );
  HST.pop_frame ()

let main () : HST.Stack (unit) (fun _ -> True) (fun _ _ _ -> True) =
  HST.push_frame ();
  let d : dll UInt32.t = dll_new () in
  let n1 = node_of 1ul in
  let n2 = node_of 2ul in
  dll_insert_at_head d n1;
  dll_insert_at_tail d n2;
  let h0 = HST.get () in
  let n1' = dll_head d in
  let t = node_val n1' in
  assert (t == 1ul); // Yay!
  HST.pop_frame ()
