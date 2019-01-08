module Example

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module DLL = DoublyLinkedListIface

let main () : HST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  let open DLL in
  HST.push_frame ();
  let d : dll UInt32.t = dll_new () in
  let n1 = node_of 1ul in
  // let h0 = HST.get () in assert (g_node_val h0 n1 = 1ul);
  let n2 = node_of 2ul in
  // let h1 = HST.get () in assert (g_node_val h1 n1 = 1ul); assert (g_node_val h1 n2 = 2ul);
  dll_insert_at_head d n1;
  HST.pop_frame ()
