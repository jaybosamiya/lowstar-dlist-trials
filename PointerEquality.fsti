module PointerEquality

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open C.Nullity

(** Allow comparing pointers *)
inline_for_extraction
val ptr_eq:
  #a:Type ->
  p:pointer a ->
  q:pointer a ->
  ST bool
    (requires (fun h -> live h p /\ live h q))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> (p==q))))
