module Example

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module DLL = DoublyLinkedListIface
module L = FStar.List.Tot

open DLL

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
