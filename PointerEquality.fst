module PointerEquality

let ptr_eq #a p q =
  assume (hasEq (pointer a));
  op_Equality #(pointer a) p q

assume
val compare_addrs_aux:
  #a:Type ->
  p:pointer a ->
  q:pointer a ->
  Tot (b:bool{b <==> (as_addr p = as_addr q)})

let compare_addrs = compare_addrs_aux
