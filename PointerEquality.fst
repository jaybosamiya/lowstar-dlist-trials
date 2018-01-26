module PointerEquality

let ptr_eq #a p q =
  assume (hasEq (pointer a));
  op_Equality #(pointer a) p q
