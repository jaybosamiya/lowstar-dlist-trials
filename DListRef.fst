module DListRef

open FStar
open FStar.Ghost
open FStar.Option
open FStar.Seq
open FStar.Ref

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
  (let (a:_{isSome a}) = a in // workaround for not using two phase type checker
   let (b:_{isSome b}) = b in
   addr_of (getSome a) <> addr_of (getSome b))

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let not_aliased0 (#t:Type) (a:ref t) (b:option (ref t)) : GTot Type0 =
  isNone b \/
  (let (b:_{isSome b}) = b in // workaround for not using two phase type checker
   addr_of a <> addr_of (getSome b))

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

let (==$) (#t:Type) (a:option (ref t)) (b:ref t) =
  isSome a /\
  (let (a:_{isSome a}) = a in // workaround for not using two phase type checker
   addr_of (getSome a) = addr_of b)

logic
let ( |> ) (#t:Type) (a:dlist t) (b:ref (dlist t)) : GTot Type0 =
  a.flink ==$ b

logic
let ( <| ) (#t:Type) (a:ref (dlist t)) (b: dlist t) : GTot Type0 =
  b.blink ==$ a

irreducible
let ( =|> ) (#t:Type) (a:ref (dlist t)) (b:ref (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 b (a@h0).blink))
    (ensures (fun h1 _ h2 ->
         modifies (only a) h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         b@h1 == b@h2 /\
         (a@h2) |> b)) =
  a := { !a with flink = Some b }

irreducible
let ( <|= ) (#t:Type) (a:ref (dlist t)) (b:ref (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 a (b@h0).flink))
    (ensures (fun h1 _ h2 ->
         modifies (only b) h1 h2 /\
         dlist_is_valid h2 b /\
         a@h1 == a@h2 /\
         (b@h1).p == (b@h2).p /\
         (b@h1).flink == (b@h2).flink /\
         a <| (b@h2))) =
  b := { !b with blink = Some a }

irreducible
let ( !=|> ) (#t:Type) (a:ref (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies (only a) h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         (a@h2).flink == None)) =
  a := { !a with flink = None }

irreducible
let ( !<|= ) (#t:Type) (a:ref (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies (only a) h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).flink == (a@h2).flink /\
         (a@h2).blink == None)) =
  a := { !a with blink = None }

unfold let (~.) (#t:Type) (a:t) : Tot (erased (seq t)) = hide (Seq.create 1 a)
unfold let (^+) (#t:Type) (a:t) (b:erased (seq t)) : Tot (erased (seq t)) = elift2 Seq.cons (hide a) b
unfold let (+^) (#t:Type) (a:erased (seq t)) (b:t) : Tot (erased (seq t)) = elift2 Seq.snoc a (hide b)

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
  (forall i. {:pattern ((nodes.[i]@h0).flink)}
     ((0 <= i /\ i < len - 1) ==>
      nodes.[i]@h0 |> nodes.[i+1]))

logic
let blink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern ((nodes.[i]@h0).blink)}
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
  (forall i. {:pattern (nodes.[i])}
     dlist_is_valid h0 nodes.[i])

logic
let all_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
    let nodes = reveal h.nodes in
    (forall i j. {:pattern (nodes.[i]); (nodes.[j])}
       (0 <= i /\ i < j /\ j < Seq.length nodes) ==>
       (let (i:nat{i < Seq.length nodes}) = i in // workaround for not using two phase type checker
        let (j:nat{j < Seq.length nodes}) = j in
        addr_of nodes.[i] <> addr_of nodes.[j]))

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

// logic
let contains_by_addr (#t:Type) (s:seq (ref t)) (x:ref t) : GTot Type0 =
  (exists i. addr_of s.[i] == addr_of x)

logic
let member_of (#t:eqtype) (h0:heap) (h:dlisthead t) (e:ref (dlist t)) : GTot Type0 =
  let nodes = reveal h.nodes in
  nodes `contains_by_addr` e

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

let is_singleton (#t:Type) (h:nonempty_dlisthead t) : Tot bool =
  compare_addrs (getSome h.lhead) (getSome h.ltail)

val nonempty_singleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ is_singleton h))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) == 1))
let nonempty_singleton_properties #t h = ()

val nonempty_nonsingleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ ~(compare_addrs (getSome h.lhead) (getSome h.ltail))))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) > 1))
let nonempty_nonsingleton_properties #t h = ()

val ghost_append_properties: #t:Type -> a:t -> b:erased (seq t) ->
  Lemma (let r = a ^+ b in
         forall i j. {:pattern ((reveal b).[i] == (reveal r).[j])}
           j = i + 1 /\ 0 <= i /\ i < length (reveal b) ==> (reveal b).[i] == (reveal r).[j])
let ghost_append_properties #t a b = ()

#set-options "--z3rlimit 50 --z3refresh"

val dlisthead_update_head: #t:eqtype -> h:nonempty_dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies (e ^+^ (getSome h.lhead)) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_head (#t:eqtype) (h:nonempty_dlisthead t) (e:ref (dlist t)) =
  let h1 = ST.get () in
  let Some n = h.lhead in
  !<|= e;
  e =|> n;
  e <|= n;
  let previously_singleton = compare_addrs n (getSome h.ltail) in
  if previously_singleton
  then (
    { lhead = Some e ; ltail = Some n ; nodes = e ^+ h.nodes }
  ) else (
    let y = { lhead = Some e ; ltail = h.ltail ; nodes = e ^+ h.nodes } in
    let h2 = ST.get () in
    assert (
      let ynodes = reveal y.nodes in
      let hnodes = reveal h.nodes in
      (forall (i:nat{2 <= i /\ i < Seq.length ynodes /\ i-1 < Seq.length hnodes}).
         {:pattern (ynodes.[i]@h2)}
         ynodes.[i]@h2 == hnodes.[i-1]@h1)); // OBSERVE
    y
  )

#reset-options

val insertHeadList : #t:eqtype -> h:dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 ->
         (isSome h.lhead ==>
          modifies (e ^+^ (getSome h.lhead)) h1 h2) /\
         (~(isSome h.lhead) ==>
          modifies (only e) h1 h2) /\
         dlisthead_is_valid h2 y))
let insertHeadList #t h e =
  if isSome h.lhead
  then dlisthead_update_head h e
  else singletonlist e

#set-options "--z3rlimit 25 --z3refresh"

val dlisthead_update_tail: #t:eqtype -> h:nonempty_dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies (e ^+^ (getSome h.ltail)) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_tail #t h e =
  let h1 = ST.get () in
  let previously_singleton = is_singleton h in
  let Some n = h.ltail in
  !=|> e;
  n =|> e;
  n <|= e;
  if previously_singleton
  then (
    { lhead = Some n ; ltail = Some e ; nodes = h.nodes +^ e }
  ) else (
    let y = { lhead = h.lhead ; ltail = Some e ; nodes = h.nodes +^ e } in
    let h2 = ST.get () in
    assert (
      let ynodes = reveal y.nodes in
      let hnodes = reveal h.nodes in
      (forall (i:nat{0 <= i /\ i < Seq.length ynodes - 2 /\ i < Seq.length hnodes - 1}).
         {:pattern (ynodes.[i]@h2)}
         ynodes.[i]@h2 == hnodes.[i]@h1)); // OBSERVE
    y
  )

#reset-options

val insertTailList : #t:eqtype -> h:dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 ->
         (isSome h.ltail ==>
          modifies (e ^+^ (getSome h.ltail)) h1 h2) /\
         (~(isSome h.lhead) ==>
          modifies (only e) h1 h2) /\
         dlisthead_is_valid h2 y))
let insertTailList #t h e =
  if isSome h.ltail
  then dlisthead_update_tail h e
  else singletonlist e

unfold let ghost_tail (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  hide (Seq.tail (reveal s))

#set-options "--z3rlimit 20"

val dlisthead_remove_head: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h))
    (ensures (fun h1 y h2 ->
         (is_singleton h ==>
          modifies (only (getSome h.lhead)) h1 h2) /\
         (~(is_singleton h) ==>
          modifies ((getSome h.lhead) ^+^ (reveal h.nodes).[1]) h1 h2) /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_head #t h =
  let h1 = ST.get () in
  let Some n = h.lhead in
  if is_singleton h
  then (
    empty_list
  ) else (
    let Some next = (!n).flink in
    recall next;
    // unlink them
    !=|> n;
    !<|= next;
    let Some htail = h.ltail in
    if compare_addrs htail next then ( // we are left with a singleton
      singletonlist next
    ) else (
      let y = { lhead = Some next ; ltail = h.ltail ; nodes = ghost_tail h.nodes } in
      let h2 = ST.get () in
      assert (
        let ynodes = reveal y.nodes in
        let hnodes = reveal h.nodes in
        (forall (i:nat{1 <= i /\ i < Seq.length ynodes /\ i+1 < Seq.length hnodes}).
                  {:pattern (ynodes.[i]@h2)}
           ynodes.[i]@h2 == hnodes.[i+1]@h1)); // OBSERVE
      y
    )
  )

#reset-options

unfold let ghost_unsnoc (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  let x = reveal s in
  let l = length x - 1 in
  hide (slice x 0 l)

#set-options "--z3rlimit 50"

val dlisthead_remove_tail: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h))
    (ensures (fun h1 y h2 ->
         (is_singleton h ==>
          modifies (only (getSome h.ltail)) h1 h2) /\
         (~(is_singleton h) ==>
          (let nodes = reveal h.nodes in
          modifies ((getSome h.ltail) ^+^ nodes.[length nodes - 2]) h1 h2)) /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_tail #t h =
  let h1 = ST.get () in
  if is_singleton h then (
    empty_list
  ) else (
    let Some n = h.ltail in
    let Some prev = (!n).blink in
    recall prev;
    //unlink them
    !<|= n;
    !=|> prev;
    let Some hhead = h.lhead in
    if compare_addrs hhead prev then ( // we are left with a singleton
      singletonlist prev
    ) else (
      let y = { lhead = h.lhead ; ltail = Some prev ; nodes = ghost_unsnoc h.nodes } in
      let h2 = ST.get () in
      assert (
        let ynodes = reveal y.nodes in
        let hnodes = reveal h.nodes in
        (forall (i:nat{0 <= i /\ i < Seq.length ynodes - 1 /\ i < Seq.length hnodes - 2}).
                  {:pattern (ynodes.[i]@h2)}
           ynodes.[i]@h2 == hnodes.[i]@h1)); // OBSERVE
      y
    )
  )

#reset-options

let rec get_ref_index (#t:Type) (s:seq (ref t)) (x:ref t{s `contains_by_addr` x}) :
  GTot (i:nat{i < Seq.length s})
    (decreases (Seq.length s)) =
  contains_elim s x;
  let h, t = Seq.head s, Seq.tail s in
  if compare_addrs h x then 0 else (
    contains_cons h t x;
    1 + get_ref_index t x)

val lemma_get_ref_index : #t:Type -> s:seq (ref t) -> x:ref t{s `contains_by_addr` x} ->
  Lemma (ensures (
    addr_of s.[get_ref_index s x] = addr_of x))
    (decreases (Seq.length s))
    [SMTPat (addr_of s.[get_ref_index s x])]
let rec lemma_get_ref_index #t s x =
  contains_elim s x;
  let h, t = Seq.head s, Seq.tail s in
  if compare_addrs h x then () else (
    contains_cons h t x;
    lemma_get_ref_index t x)

val split_seq_at_element : #t:Type -> s:seq (ref t) -> x:ref t{s `contains_by_addr` x} ->
  GTot (v:(seq (ref t) * ref t * seq (ref t)){
      let l, m, r = v in
      s == append l (cons m r) /\
      addr_of m == addr_of x
  })
let split_seq_at_element #t s x =
  let i = get_ref_index s x in
  let l, mr = Seq.split s i in
  lemma_split s i;
  l, head mr, tail mr

#reset-options "--z3rlimit 1 --detail_errors --z3rlimit_factor 20"

val dlisthead_remove_strictly_mid: #t:eqtype -> h:nonempty_dlisthead t -> e:ref (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\
                         member_of h0 h e /\
                         not_aliased0 e h.lhead /\ not_aliased0 e h.ltail))
    (ensures (fun h1 y h2 ->
         isSome (e@h1).flink /\ isSome (e@h1).blink /\
         dlist_is_valid h2 e /\
         isNone (e@h2).flink /\ isNone (e@h2).blink /\
         modifies (e ^++ (getSome (e@h1).flink) ^+^ (getSome (e@h1).blink)) h1 h2 /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_strictly_mid #t h e =
  admit ();
  assert (Seq.length (reveal h.nodes) >= 3); // would want to start from here
  h // TODO: Actually do something

/// Useful code that can be copied over below

(*
    assert (all_nodes_contained h2 y);
    assert (dlisthead_ghostly_connections h2 y);
    assert (flink_valid h2 y);
    assert (blink_valid h2 y);
    assert (elements_are_valid h2 y);
    assert (elements_dont_alias1 h2 y);
    assert (elements_dont_alias2 h2 y);
    assert (all_elements_distinct h2 y);
*)
