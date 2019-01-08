module Example

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module DLL = DoublyLinkedListIface

let main () : HST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  HST.push_frame ();
  let d : DLL.dll UInt32.t = DLL.dll_new () in
  let n1 = DLL.node_of 1ul in
  let n2 = DLL.node_of 2ul in
  let h0 = HST.get () in
  assume (DLL.fp_node n1 `B.loc_disjoint` DLL.fp_dll h0 d);
  DLL.dll_insert_at_head d n1;
  HST.pop_frame ()
