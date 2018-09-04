module Gpointers

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module Mod = LowStar.Modifies

type gpointer t = B.pointer t
type gpointer_or_null t = B.pointer_or_null t

let disjoint (#t:Type) (a b: gpointer t) = B.as_addr a <> B.as_addr b

let null #t : gpointer_or_null t = B.null #t

assume val is_null (p:gpointer_or_null 't) : Tot (b:bool{b <==> p == null})
let is_not_null (p:gpointer_or_null 't) = not (is_null p)

let lemma_is_null (p:gpointer_or_null 't) :
  Lemma
    (ensures (is_null p <==> B.g_is_null p))
    [SMTPat (is_null p)]
    = B.null_unique p

let test_null #t =
  let p : gpointer_or_null t = null in
  assert (is_null p)

let ( := ) (a:gpointer 't) (b:'t) = B.upd a 0ul b
let ( ! ) (a:gpointer 't) = B.index a 0ul

let recall (#t:Type) (p: gpointer_or_null t) = B.recall p

val non_null:
  #t:Type ->
  a:gpointer_or_null t{is_not_null a} ->
  b:gpointer t
let non_null #t a = a

val lemma_non_null :
  #t:Type ->
  a:gpointer_or_null t{is_not_null a} ->
  Lemma (ensures (a == non_null a))
    [SMTPat (non_null a)]
let lemma_non_null #t a = ()

val of_non_null:
  #t:Type ->
  a:gpointer t ->
  b:gpointer_or_null t
let of_non_null #t a = a

val lemma_of_non_null:
  #t:Type ->
  a:gpointer t ->
  Lemma (ensures (is_not_null (of_non_null a)) /\ (of_non_null a == a))
let lemma_of_non_null #t a = ()

let heap = HS.mem
let contains #a #rrel #rel h b = B.live #a #rrel #rel h b

(** Dereference a gpointer. NOTE: To get a sane result, also need to
    prove that the pointer is on the heap. *)
let (@) (a:gpointer 't) (h0:heap) = B.get h0 a 0
(** Dereference a non-null gpointer_or_null. NOTE: To get a sane
    result, also need to prove that the pointer is on the heap. *)
let (^@) (a:gpointer_or_null 't{is_not_null a}) (h0:heap) = (non_null a) @ h0

let (==$) (#t:Type) (a:gpointer_or_null t) (b:gpointer t) =
  is_not_null a /\
  (let (a:_{is_not_null a}) = a in // workaround for not using two phase type checker
   (non_null a) == b)

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased (#t:Type) (a:gpointer_or_null t) (b:gpointer_or_null t) : GTot Type0 =
  Mod.loc_disjoint (Mod.loc_buffer a) (Mod.loc_buffer b)

let modifies_1 (a:gpointer 'a) h0 h1 =
  Mod.modifies (Mod.loc_buffer a) h0 h1
