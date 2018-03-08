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

unfold let (@) (a:ref 't) (h0:heap{h0 `contains` a}) = sel h0 a
unfold let (^@) (a:option (ref 't){isSome a}) (h0:heap{h0 `contains` (getSome a)}) = (getSome a) @ h0

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
let not_aliased00 (#t:Type) (a:ref t) (b:ref t) : GTot Type0 =
  addr_of a <> addr_of b

logic
let dlist_is_valid' (#t:Type) (h0:heap) (n:dlist t) : GTot Type0 =
  not_aliased n.flink n.blink

// logic
let dlist_is_valid (#t:Type) (h0:heap) (n:ref (dlist t)) : GTot Type0 =
  h0 `contains` n /\
  dlist_is_valid' h0 (n@h0)

unfold
let (==$) (#t:Type) (a:option (ref t)) (b:ref t) =
  isSome a /\
  addr_of (getSome a) = addr_of b

unfold logic
let ( |> ) (#t:Type) (a:dlist t) (b:ref (dlist t)) : GTot Type0 =
  a.flink ==$ b

unfold logic
let ( <| ) (#t:Type) (a:ref (dlist t)) (b: dlist t) : GTot Type0 =
  b.blink ==$ a

let ( =|> ) (#t:Type) (a:ref (dlist t)) (b:ref (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 b (a@h0).blink))
    (ensures (fun h1 _ h2 ->
         modifies (only a) h1 h2 /\
         dlist_is_valid h2 a /\
         (forall (f:dlist t -> Type0) x. {:pattern f (x@h2)}
            h1 `contains` x /\
            f (x@h1) /\ not_aliased00 x a ==> f (x@h2)) /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         b@h1 == b@h2 /\
         (a@h2) |> b)) =
  a := { !a with flink = Some b }

let ( <|= ) (#t:Type) (a:ref (dlist t)) (b:ref (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 a (b@h0).flink))
    (ensures (fun h1 _ h2 ->
         modifies (only b) h1 h2 /\
         dlist_is_valid h2 b /\
         (forall (f:dlist t -> Type0) x. {:pattern f (x@h2)}
            h1 `contains` x /\
            f (x@h1) /\ not_aliased00 x b ==> f (x@h2)) /\
         a@h1 == a@h2 /\
         (b@h1).p == (b@h2).p /\
         (b@h1).flink == (b@h2).flink /\
         a <| (b@h2))) =
  b := { !b with blink = Some a }

let ( !=|> ) (#t:Type) (a:ref (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies (only a) h1 h2 /\
         dlist_is_valid h2 a /\
         (forall (f:dlist t -> Type0) x. {:pattern f (x@h2)}
            h1 `contains` x /\
            f (x@h1) /\ not_aliased00 x a ==> f (x@h2)) /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         (a@h2).flink == None)) =
  a := { !a with flink = None }

let ( !<|= ) (#t:Type) (a:ref (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies (only a) h1 h2 /\
         dlist_is_valid h2 a /\
         (forall (f:dlist t -> Type0) x. {:pattern f (x@h2)}
            h1 `contains` x /\
            f (x@h1) /\ not_aliased00 x a ==> f (x@h2)) /\
         (a@h1).p == (a@h2).p /\
         (a@h2).flink == (a@h2).flink /\
         (a@h2).blink == None)) =
  a := { !a with blink = None }

unfold let (~.) (#t:Type) (a:t) : Tot (erased (seq t)) = hide (Seq.create 1 a)
unfold let (^+) (#t:Type) (a:t) (b:erased (seq t)) : Tot (erased (seq t)) = elift2 Seq.cons (hide a) b

logic
let all_nodes_contained (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  (isSome h.lhead ==> h0 `contains` (getSome h.lhead)) /\
  (isSome h.ltail ==> h0 `contains` (getSome h.ltail)) /\
  (forall i. {:pattern (h0 `contains` nodes.[i])}
     h0 `contains` nodes.[i])

logic
let flink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern (nodes.[i]@h0 |> nodes.[i+1])}
     ((0 <= i /\ i < len - 1) ==>
      nodes.[i]@h0 |> nodes.[i+1]))

logic
let blink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern (nodes.[i-1] <| nodes.[i]@h0)}
     ((1 <= i /\ i < len) ==>
      nodes.[i-1] <| nodes.[i]@h0))

logic
let dlisthead_ghostly_connections (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  all_nodes_contained h0 h /\
  ~empty ==> (
    h.lhead ==$ nodes.[0] /\
    h.ltail ==$ nodes.[len-1] /\
    isNone (h.lhead^@h0).blink /\
    isNone (h.ltail^@h0).flink)

logic
let elements_dont_alias1 (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)}
     0 < i /\ i < j /\ j < length nodes ==>
   not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)

logic
let elements_dont_alias2 (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)}
     0 < i /\ i < j /\ j < length nodes ==>
   not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let elements_dont_alias (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  elements_dont_alias1 h0 h /\
  elements_dont_alias2 h0 h

logic
let elements_are_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern (dlist_is_valid h0 nodes.[i])}
     dlist_is_valid h0 nodes.[i])

logic
let all_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
    let nodes = reveal h.nodes in
    (forall i j. {:pattern (nodes.[i]@h0 =!= nodes.[j]@h0)}
       (0 <= i /\ i < j /\ j < Seq.length nodes) ==>
     addr_of nodes.[i] <> addr_of nodes.[j])

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
  (requires (fun h0 -> h0 `contains` e))
  (ensures (fun h0 y h1 -> modifies (only e) h0 h1 /\ dlisthead_is_valid h1 y))
let singletonlist #t e =
  !<|= e; !=|> e;
  { lhead = Some e ; ltail = Some e ; nodes = ~. e }

logic
let member_of (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot bool =
  let cmp x : GTot bool = addr_of x = addr_of e in
  let r = Seq.ghost_find_l cmp (reveal h.nodes) in
  isSome r

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let has_nothing_in (#t:eqtype) (h0:heap)
    (h:dlisthead t{dlisthead_is_valid h0 h})
    (e:ref (dlist t){h0 `contains` e})
  : GTot Type0 =
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

val dlisthead_make_valid_singleton: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 ->
         h0 `contains` (getSome h.lhead) /\
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
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies (e ^+^ (getSome h.lhead)) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_head (#t:eqtype) (h:nonempty_dlisthead t) (e:ref (dlist t)) =
  let h1 = ST.get () in
  let Some n = h.lhead in
  !<|= e;
  e =|> n;
  let previously_singleton = compare_addrs n (getSome h.ltail) in
  let h' = ST.get () in
  assert (addr_of n == addr_of (reveal h.nodes).[0]);
  assert ((n@h1) == (((reveal h.nodes).[0])@h1));
  assert (not_aliased0 e (((reveal h.nodes).[0])@h1).flink);
  assert (not_aliased0 e (((reveal h.nodes).[0])@h').flink);
  assert (not_aliased0 e (n@h1).flink);
  assert (not_aliased0 e (n@h').flink);
  e <|= n;
  if previously_singleton
  then (
    { lhead = Some e ; ltail = Some n ; nodes = e ^+ ~. n }
  ) else (
    admit ();
    let y = { lhead = Some e ; ltail = h.ltail ; nodes = e ^+ h.nodes } in
    let h2 = ST.get () in
    admit ();
    y
  )
