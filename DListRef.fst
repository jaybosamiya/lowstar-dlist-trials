module DListRef

open FStar
open FStar.Ghost
open FStar.Option
open FStar.Seq
open FStar.Ref

#set-options "--use_two_phase_tc true"

unopteq
(** Node of a doubly linked list *)
type dlist (t:Type0) = {
  (* forward link *)
  flink: option (ref (dlist t));
  (* backward link *)
  blink: option (ref (dlist t));
  (* payload *)
  p: t;
}

unopteq
(** Doubly linked list head *)
type dlisthead (t:Type0) ={
  lhead: option (ref (dlist t));
  ltail: option (ref (dlist t));
  nodes: erased (seq (ref (dlist t)));
}

(** Initialize an element of a doubly linked list *)
val empty_entry: #t:Type -> payload:t -> dlist t
let empty_entry #t payload =
  { flink = None ; blink = None ; p = payload }

(** Initialize a doubly linked list head *)
val empty_list: #t:Type -> dlisthead t
let empty_list #t =
  { lhead = None ; ltail = None ; nodes = hide createEmpty }

val getSome: (a:option 'a{isSome a}) -> (b:'a{a == Some b})
let getSome a = Some?.v a

unfold let (@) (a:ref 't) (h0:heap) = sel h0 a
unfold let (^@) (a:option (ref 't){isSome a}) (h0:heap) = (getSome a) @ h0

unfold let (.[]) (s:seq 'a) (n:nat{n < length s}) = index s n

val not_aliased: #t:Type -> (a:option (ref t)) -> (b:option (ref t)) -> Type0
let not_aliased #t a b =
  let _ = () in // UGLY workaround. See https://github.com/FStarLang/FStar/issues/638
  isNone a \/ isNone b \/
  addr_of (getSome a) <> addr_of (getSome b)

val not_aliased0: #t:Type -> (a:ref t) -> (b:option (ref t)) -> Type0
let not_aliased0 #t a b =
  let _ = () in // UGLY workaround. See https://github.com/FStarLang/FStar/issues/638
  isNone b \/
  addr_of a <> addr_of (getSome b)

val dlist_is_valid: #t:Type -> n:dlist t -> Type0
let dlist_is_valid #t n =
  not_aliased n.flink n.blink

val flink_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let flink_valid #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  (forall i. {:pattern (nodes.[i]@h0).flink}
     ((0 <= i /\ i < len - 1) ==>
      (nodes.[i]@h0).flink == Some nodes.[i+1]))

val blink_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let blink_valid #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  (forall i. {:pattern (nodes.[i]@h0).blink}
     ((1 <= i /\ i < len) ==>
      (nodes.[i]@h0).blink == Some nodes.[i-1]))

val dlisthead_ghostly_connections: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let dlisthead_ghostly_connections #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  ~empty ==> (
    isSome h.lhead /\ isSome h.ltail /\
    isNone (h.lhead^@h0).blink /\
    isNone (h.ltail^@h0).flink /\
    h.lhead == Some nodes.[0] /\
    h.ltail == Some nodes.[len-1])

val elements_dont_alias1: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let elements_dont_alias1 #t h0 h =
  let nodes = reveal h.nodes in
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)}
     i <> j ==> not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)

val elements_dont_alias2: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let elements_dont_alias2 #t h0 h =
  let nodes = reveal h.nodes in
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)}
     i <> j ==> not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)

val elements_dont_alias: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let elements_dont_alias #t h0 h =
  let _ = () in // UGLY workaround. See https://github.com/FStarLang/FStar/issues/638
  elements_dont_alias1 h0 h /\
  elements_dont_alias2 h0 h

val elements_are_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let elements_are_valid #t h0 h =
  let nodes = reveal h.nodes in
  (forall i. {:pattern (dlist_is_valid (nodes.[i]@h0))}
     dlist_is_valid (nodes.[i]@h0))

val dlisthead_is_valid: #t:Type -> h0:heap -> h:dlisthead t -> Type0
let dlisthead_is_valid #t h0 h =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  (empty ==> isNone h.lhead /\ isNone h.ltail) /\
  (~empty ==> dlisthead_ghostly_connections h0 h /\
              flink_valid h0 h /\
              blink_valid h0 h) /\
  elements_are_valid h0 h /\
  elements_dont_alias h0 h

let test1 () : Tot unit = assert (forall h0 t. dlisthead_is_valid h0 (empty_list #t))

val singletonlist: #t:eqtype -> e:ref (dlist t) ->
  ST (dlisthead t)
  (requires (fun _ -> True))
  (ensures (fun h0 y h1 -> modifies (only e) h0 h1 /\ dlisthead_is_valid h1 y))
let singletonlist #t e =
  e := { !e with blink = None; flink = None };
  { lhead = Some e ; ltail = Some e ; nodes = hide (Seq.create 1 e) }

let member_of (#t:eqtype) (h:dlisthead t) (e:ref (dlist t)) : GTot Type0 =
  (exists x. {:pattern (addr_of e = addr_of x)}
     Seq.contains (reveal h.nodes) x /\ addr_of e = addr_of x)

// logic
let has_nothing_in (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot Type0 =
  (let nodes = reveal h.nodes in
   (forall i. {:pattern (addr_of nodes.[i])}
      addr_of e <> addr_of nodes.[i]) /\
   (forall i. {:pattern (nodes.[i]@h0).flink}
      (not_aliased0 e (nodes.[i]@h0).flink /\
       not_aliased (e@h0).flink (nodes.[i]@h0).flink /\
       not_aliased (e@h0).blink (nodes.[i]@h0).flink)) /\
   (forall i. {:pattern (nodes.[i]@h0).blink}
      (not_aliased0 e (nodes.[i]@h0).blink) /\
      not_aliased (e@h0).flink (nodes.[i]@h0).blink /\
      not_aliased (e@h0).blink (nodes.[i]@h0).blink))

type nonempty_dlisthead t = (h:dlisthead t{isSome h.lhead /\ isSome h.ltail})

unfold let (~.) (#t:Type) (a:t) : Tot (erased (seq t)) = hide (Seq.create 1 a)
unfold let (^+) (#t:Type) (a:t) (b:erased (seq t)) : Tot (erased (seq t)) = elift2 Seq.cons (hide a) b

val dlisthead_make_valid_singleton: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 ->
         isNone (h.lhead^@h0).flink /\ isNone (h.lhead^@h0).blink))
    (ensures (fun h1 y h2 -> modifies_none h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_make_valid_singleton #t h =
  let Some e = h.lhead in
  { h with ltail = h.lhead ; nodes = ~. e }

unfold let ghost_tail (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  hide (Seq.tail (reveal s))

val ghost_tail_properties :
  #t:Type ->
  s:erased (seq t){Seq.length (reveal s) > 0} ->
  Lemma (
    let l = Seq.length (reveal s) in
    let t = ghost_tail s in
    let s0 = reveal s in
    let t0 = reveal t in
    Seq.length t0 = Seq.length s0 - 1 /\
    (forall i j. {:pattern (t0.[i] == s0.[j])}
       j = i + 1 /\ 0 <= i /\ i < Seq.length t0 ==> t0.[i] == s0.[j]))
let ghost_tail_properties #t s = ()

#set-options "--z3rlimit 1 --detail_errors --z3rlimit_factor 20"

val ghost_append_properties: #t:Type -> a:t -> b:erased (seq t) ->
  Lemma (let r = a ^+ b in
         forall i j. {:pattern ((reveal b).[i] == (reveal r).[j])}
           j = i + 1 /\ 0 <= i /\ i < length (reveal b) ==> (reveal b).[i] == (reveal r).[j])
let ghost_append_properties #t a b = ()

val dlisthead_update_head: #t:eqtype -> h:nonempty_dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid (e@h0) /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies (e ^+^ (getSome h.lhead)) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_head (#t:eqtype) (h:nonempty_dlisthead t) (e:ref (dlist t)) =
  let h1 = ST.get () in
  assert (has_nothing_in h1 h e);
  // admit ();
  assert (
    let nodes = reveal h.nodes in
    forall i. addr_of e <> addr_of nodes.[i]);
  assert (
    let nodes = reveal h.nodes in
    addr_of e <> addr_of nodes.[0]);
  admit ();
  let Some n = h.lhead in
  e := { !e with blink = None; flink = Some n };
  let previously_singleton = compare_addrs n (getSome h.ltail) in
  n := { !n with blink = Some e };
  if previously_singleton
  then (
    let y = { lhead = Some e ; ltail = Some n ; nodes = e ^+ ~. n } in
    y
  ) else (
    admit ();
    let y = { lhead = Some e ; ltail = h.ltail ; nodes = e ^+ n ^+ (ghost_tail h.nodes) } in
    y
  )
