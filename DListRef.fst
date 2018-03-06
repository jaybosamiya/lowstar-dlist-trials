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

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased (#t:Type) (a:option (ref t)) (b:option (ref t)) : GTot Type0 =
  isNone a \/ isNone b \/
  addr_of (getSome a) <> addr_of (getSome b)

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased0 (#t:Type) (a:ref t) (b:option (ref t)) : GTot Type0 =
  isNone b \/
  addr_of a <> addr_of (getSome b)

logic
let dlist_is_valid (#t:Type) (n:dlist t) : GTot Type0 =
  not_aliased n.flink n.blink

unfold let (==$) (#t:Type) (a:option (ref t){isSome a}) (b:ref t) = addr_of (getSome a) = addr_of b

logic
let flink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  (forall i. {:pattern (nodes.[i]@h0).flink}
     ((0 <= i /\ i < len - 1) ==>
      isSome (nodes.[i]@h0).flink /\
      (nodes.[i]@h0).flink ==$ nodes.[i+1]))

logic
let blink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  (forall i. {:pattern (nodes.[i]@h0).blink}
     ((1 <= i /\ i < len) ==>
      isSome (nodes.[i]@h0).blink /\
      (nodes.[i]@h0).blink ==$ nodes.[i-1]))

logic
let dlisthead_ghostly_connections (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  ~empty ==> (
    isSome h.lhead /\ isSome h.ltail /\
    isNone (h.lhead^@h0).blink /\
    isNone (h.ltail^@h0).flink /\
    h.lhead ==$ nodes.[0] /\
    h.ltail ==$ nodes.[len-1])

logic
let elements_dont_alias1 (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)}
     i <> j ==> not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)

logic
let elements_dont_alias2 (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)}
     i <> j ==> not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let elements_dont_alias (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  elements_dont_alias1 h0 h /\
  elements_dont_alias2 h0 h

logic
let elements_are_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  (forall i. {:pattern (dlist_is_valid (nodes.[i]@h0))}
     dlist_is_valid (nodes.[i]@h0))

logic
let all_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
    let nodes = reveal h.nodes in
    (forall i j. {:pattern (nodes.[i]@h0 =!= nodes.[j]@h0)}
       (0 <= i /\ i < j /\ j < Seq.length nodes) ==>
     nodes.[i]@h0 =!= nodes.[j]@h0)

logic
let dlisthead_is_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  (empty ==> isNone h.lhead /\ isNone h.ltail) /\
  (~empty ==> dlisthead_ghostly_connections h0 h /\
              flink_valid h0 h /\
              blink_valid h0 h) /\
  elements_are_valid h0 h /\
  elements_dont_alias h0 h /\
  all_elements_distinct h0 h

let test1 () : Tot unit = assert (forall h0 t. dlisthead_is_valid h0 (empty_list #t))

val singletonlist: #t:eqtype -> e:ref (dlist t) ->
  ST (dlisthead t)
  (requires (fun _ -> True))
  (ensures (fun h0 y h1 -> modifies (only e) h0 h1 /\ dlisthead_is_valid h1 y))
let singletonlist #t e =
  e := { !e with blink = None; flink = None };
  { lhead = Some e ; ltail = Some e ; nodes = hide (Seq.create 1 e) }

logic
let member_of (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot bool =
  let cmp x : GTot bool = addr_of x = addr_of e in
  let r = Seq.ghost_find_l cmp (reveal h.nodes) in
  isSome r

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let has_nothing_in (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot Type0 =
  (~(member_of h0 h e)) /\
  (not_aliased0 e h.lhead) /\
  (not_aliased0 e h.ltail) /\
  (let nodes = reveal h.nodes in
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

let foo (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 1}) : Lemma
  (Seq.last (reveal (ghost_tail s)) == Seq.last (reveal s)) = ()

#set-options "--z3rlimit 1 --detail_errors --z3rlimit_factor 20"

val nonempty_nonsingleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ ~(compare_addrs (getSome h.lhead) (getSome h.ltail))))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) > 1))

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
  let Some n = h.lhead in
  e := { !e with blink = None; flink = Some n };
  let previously_singleton = compare_addrs n (getSome h.ltail) in
  n := { !n with blink = Some e };
  if previously_singleton
  then (
    { lhead = Some e ; ltail = Some n ; nodes = e ^+ ~. n }
  ) else (
    let y = { lhead = Some e ; ltail = h.ltail ; nodes = e ^+ n ^+ (ghost_tail h.nodes) } in
    let h2 = ST.get () in
    assert (isSome ((reveal h.nodes).[0]@h1).flink); // OBSERVE
    // assert (isSome (e@h2).flink);
    // assert (isSome (n@h2).flink);
    // assert (forall i. {:pattern isSome ((reveal y.nodes).[i]@h2).flink}
    //           0 <= i /\ i < 2 ==>
    //         isSome ((reveal y.nodes).[i]@h2).flink);
    // assert (forall i. {:pattern (reveal y.nodes).[i]}
    //           2 <= i /\ i < length (reveal y.nodes) ==>
    //         (reveal y.nodes).[i] == (reveal h.nodes).[i-1]);
    assert (forall i. {:pattern isSome ((reveal h.nodes).[i]@h1).flink}
              0 <= i /\ i < length (reveal h.nodes) - 1 ==>
            isSome ((reveal h.nodes).[i]@h1).flink);
    assert (forall i. {:pattern isSome ((reveal y.nodes).[i]@h2).flink}
              2 <= i /\ i < length (reveal y.nodes) - 1 ==>
            isSome ((reveal y.nodes).[i]@h2).flink);
    // admit ();
    assert (
      let h0, h = h2, y in
      let nodes = reveal h.nodes in
      let len = length nodes in
      (forall i. {:pattern (nodes.[i]@h0).flink}
         ((0 <= i /\ i < len - 1) ==>
          isSome (nodes.[i]@h0).flink /\
          (nodes.[i]@h0).flink ==$ nodes.[i+1])));

    assert (flink_valid h2 y);

    admit ();
    assume (blink_valid h2 y); // TODO: Figure out why it is unable to prove
    assume (elements_are_valid h2 y); // TODO: Figure out why it is unable to prove
    assume (elements_dont_alias h2 y); // TODO: Figure out why it is unable to prove
    assume (all_elements_distinct h2 y); // TODO: Figure out why it is unable to prove
    y
  )
