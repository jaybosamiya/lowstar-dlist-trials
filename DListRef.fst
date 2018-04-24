module DListRef

open FStar
open FStar.Ghost
open FStar.Seq
open FStar.Ref
open GpointersViaRefs

#set-options "--use_two_phase_tc true"

unopteq
(** Node of a doubly linked list *)
type dlist (t:Type0) = {
  (* forward link *)
  flink: gpointer_or_null (dlist t);
  (* backward link *)
  blink: gpointer_or_null (dlist t);
  (* payload *)
  p: t;
}

unopteq
(** Doubly linked list head *)
type dlisthead (t:Type0) ={
  lhead: gpointer_or_null (dlist t);
  ltail: gpointer_or_null (dlist t);
  nodes: erased (seq (gpointer (dlist t)));
}

(** Initialize an element of a doubly linked list *)
val empty_entry: #t:Type -> payload:t -> dlist t
let empty_entry #t payload =
  { flink = null ; blink = null ; p = payload }

(** Initialize a doubly linked list head *)
val empty_list: #t:Type -> dlisthead t
let empty_list #t =
  { lhead = null ; ltail = null ; nodes = hide createEmpty }

unfold let (.[]) (s:seq 'a) (n:nat{n < length s}) = index s n

logic
let dlist_is_valid' (#t:Type) (h0:heap) (n:dlist t) : GTot Type0 =
  not_aliased n.flink n.blink

// logic
let dlist_is_valid (#t:Type) (h0:heap) (n:gpointer (dlist t)) : GTot Type0 =
  h0 `contains` n /\
  dlist_is_valid' h0 (n@h0)

logic
let ( |> ) (#t:Type) (a:dlist t) (b:gpointer (dlist t)) : GTot Type0 =
  a.flink ==$ b

logic
let ( <| ) (#t:Type) (a:gpointer (dlist t)) (b: dlist t) : GTot Type0 =
  b.blink ==$ a

irreducible
let ( =|> ) (#t:Type) (a:gpointer (dlist t)) (b:gpointer (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 b (a@h0).blink))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         b@h1 == b@h2 /\
         (a@h2) |> b)) =
  a := { !a with flink = of_non_null b }

irreducible
let ( <|= ) (#t:Type) (a:gpointer (dlist t)) (b:gpointer (dlist t)) : ST unit
    (requires (fun h0 ->
         h0 `contains` a /\ h0 `contains` b /\
         not_aliased00 a b /\
         not_aliased0 a (b@h0).flink))
    (ensures (fun h1 _ h2 ->
         modifies_1 b h1 h2 /\
         dlist_is_valid h2 b /\
         a@h1 == a@h2 /\
         (b@h1).p == (b@h2).p /\
         (b@h1).flink == (b@h2).flink /\
         a <| (b@h2))) =
  b := { !b with blink = of_non_null a }

irreducible
let ( !=|> ) (#t:Type) (a:gpointer (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).blink == (a@h2).blink /\
         (a@h2).flink == null)) =
  a := { !a with flink = null }

irreducible
let ( !<|= ) (#t:Type) (a:gpointer (dlist t)) : ST unit
    (requires (fun h0 -> h0 `contains` a))
    (ensures (fun h1 _ h2 ->
         modifies_1 a h1 h2 /\
         dlist_is_valid h2 a /\
         (a@h1).p == (a@h2).p /\
         (a@h1).flink == (a@h2).flink /\
         (a@h2).blink == null)) =
  a := { !a with blink = null }

unfold let (~.) (#t:Type) (a:t) : Tot (erased (seq t)) = hide (Seq.create 1 a)
unfold let (^+) (#t:Type) (a:t) (b:erased (seq t)) : Tot (erased (seq t)) = elift2 Seq.cons (hide a) b
unfold let (+^) (#t:Type) (a:erased (seq t)) (b:t) : Tot (erased (seq t)) = elift2 Seq.snoc a (hide b)

let trigger_all_nodes_contained #t (h0:heap) (h:dlisthead t) i = True

logic
let all_nodes_contained (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  (is_not_null h.lhead ==> h0 `contains` (non_null h.lhead)) /\
  (is_not_null h.ltail ==> h0 `contains` (non_null h.ltail)) /\
  (forall i. {:pattern (trigger_all_nodes_contained h0 h i)}
     h0 `contains` nodes.[i])

let get_all_nodes_contained (#t:Type) (h0:heap) (h:dlisthead t) (i:nat{i < length (reveal h.nodes)}) :
  Lemma
    (requires all_nodes_contained h0 h)
    (ensures h0 `contains` (reveal h.nodes).[i]) =
  assert (trigger_all_nodes_contained h0 h i)

logic
let flink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern ((nodes.[i]@h0).flink)}
     ((0 <= i /\ i < len - 1) ==>
      (get_all_nodes_contained h0 h i;
       nodes.[i]@h0 |> nodes.[i+1])))

logic
let blink_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern ((nodes.[i]@h0).blink)}
     ((1 <= i /\ i < len) ==>
      (get_all_nodes_contained h0 h i;
       nodes.[i-1] <| nodes.[i]@h0)))

logic
let dlisthead_ghostly_connections (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  all_nodes_contained h0 h /\
  ~empty ==> (
    h.lhead ==$ nodes.[0] /\
    h.ltail ==$ nodes.[len-1] /\
    is_null (h.lhead^@h0).blink /\
    is_null (h.ltail^@h0).flink)

logic
let elements_dont_alias1 (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink)}
     0 <= i /\ i < j /\ j < length nodes ==> (
     get_all_nodes_contained h0 h i;
     get_all_nodes_contained h0 h j;
     not_aliased (nodes.[i]@h0).flink (nodes.[j]@h0).flink))

logic
let elements_dont_alias2 (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i j. {:pattern (not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink)}
     0 <= i /\ i < j /\ j < length nodes ==>
   (get_all_nodes_contained h0 h i;
    get_all_nodes_contained h0 h j;
    not_aliased (nodes.[i]@h0).blink (nodes.[j]@h0).blink))

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let elements_dont_alias (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  elements_dont_alias1 h0 h /\
  elements_dont_alias2 h0 h

let trigger_elements_are_valid (#t:Type) (h0:heap) (h:dlisthead t) i = True

logic
let elements_are_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  all_nodes_contained h0 h /\
  (forall i. {:pattern (trigger_elements_are_valid h0 h i)}
     dlist_is_valid h0 nodes.[i])

let get_elements_are_valid (#t:Type) (h0:heap) (h:dlisthead t) (i:nat{i < length (reveal h.nodes)}) :
  Lemma
    (requires elements_are_valid h0 h)
    (ensures dlist_is_valid h0 (reveal h.nodes).[i]) =
  assert (trigger_elements_are_valid h0 h i)

logic
let all_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
    let nodes = reveal h.nodes in
    (forall i j. {:pattern (disjoint nodes.[i] nodes.[j])}
       (0 <= i /\ i < j /\ j < Seq.length nodes) ==>
       (disjoint nodes.[i] nodes.[j]))

unfold logic
let dlisthead_is_valid (#t:Type) (h0:heap) (h:dlisthead t) : GTot Type0 =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  (empty ==> is_null h.lhead /\ is_null h.ltail) /\
  (~empty ==> dlisthead_ghostly_connections h0 h /\
              flink_valid h0 h /\
              blink_valid h0 h) /\
  elements_are_valid h0 h /\
  elements_dont_alias h0 h

let rec two_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) (i j:int) : Lemma
  (requires (0 <= i /\ i < j /\ j < Seq.length (reveal h.nodes)) /\
            dlisthead_ghostly_connections h0 h /\
            blink_valid h0 h /\
            elements_are_valid h0 h)
  (ensures
     (let nodes = reveal h.nodes in
      disjoint nodes.[i] nodes.[j])) =
  let nodes = reveal h.nodes in
  if 0 <= i && i < j && j < Seq.length nodes then (
    let b = FStar.StrongExcludedMiddle.strong_excluded_middle (disjoint nodes.[i] nodes.[j]) in
    if not b then (
      if i = 0 then (
        assert( is_null (nodes.[i]@h0).blink);
        get_elements_are_valid h0 h j;
        assert( is_not_null (nodes.[j]@h0).blink)
      ) else (
        get_elements_are_valid h0 h i;
        get_elements_are_valid h0 h j;
        two_elements_distinct h0 h (i - 1) (j - 1)
      )
    ) else ()
  ) else ()

let lemma_all_elements_distinct (#t:Type) (h0:heap) (h:dlisthead t) : Lemma
    (requires dlisthead_is_valid h0 h)
    (ensures all_elements_distinct h0 h) =
  let nodes = reveal h.nodes in
  let two_elements_distinct_helper (i j:int) : Lemma
    ((0 <= i /\ i < j /\ j < Seq.length nodes) ==>
       (disjoint nodes.[i] nodes.[j]))
    =
    if 0 <= i && i < j && j < Seq.length nodes then (
      two_elements_distinct h0 h i j
    ) else ()
  in
  FStar.Classical.forall_intro_2 two_elements_distinct_helper

let test1 () : Tot unit = assert (forall h0 t. dlisthead_is_valid h0 (empty_list #t))

val singletonlist: #t:eqtype -> e:gpointer (dlist t) ->
  ST (dlisthead t)
  (requires (fun h0 -> h0 `contains` e))
  (ensures (fun h0 y h1 -> modifies_1 e h0 h1 /\ dlisthead_is_valid h1 y))
let singletonlist #t e =
  !<|= e; !=|> e;
  { lhead = of_non_null e ; ltail = of_non_null e ; nodes = ~. e }

// logic
let contains_by_addr (#t:Type) (s:seq (gpointer t)) (x:gpointer t) : GTot Type0 =
  (exists i. g_ptr_eq s.[i] x)

logic
let member_of (#t:eqtype) (h0:heap) (h:dlisthead t) (e:gpointer (dlist t)) : GTot Type0 =
  let nodes = reveal h.nodes in
  nodes `contains_by_addr` e

// logic : Cannot use due to https://github.com/FStarLang/FStar/issues/638
let has_nothing_in (#t:eqtype) (h0:heap)
    (h:dlisthead t{dlisthead_is_valid h0 h})
    (e:gpointer (dlist t){h0 `contains` e})
  : GTot Type0 =
  (~(member_of h0 h e)) /\
  (not_aliased0 e h.lhead) /\
  (not_aliased0 e h.ltail) /\
  (let nodes = reveal h.nodes in
   (forall i. {:pattern (nodes.[i]@h0).flink}
      (get_all_nodes_contained h0 h i;
       (not_aliased0 e (nodes.[i]@h0).flink /\
        not_aliased (e@h0).flink (nodes.[i]@h0).flink /\
        not_aliased (e@h0).blink (nodes.[i]@h0).flink))) /\
   (forall i. {:pattern (nodes.[i]@h0).blink}
      (get_all_nodes_contained h0 h i;
       (not_aliased0 e (nodes.[i]@h0).blink) /\
        not_aliased (e@h0).flink (nodes.[i]@h0).blink /\
        not_aliased (e@h0).blink (nodes.[i]@h0).blink)))

type nonempty_dlisthead t = (h:dlisthead t{is_not_null h.lhead /\ is_not_null h.ltail})

val dlisthead_make_valid_singleton: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 ->
         h0 `contains` (non_null h.lhead) /\
         is_null (h.lhead^@h0).flink /\ is_null (h.lhead^@h0).blink))
    (ensures (fun h1 y h2 -> modifies_none h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_make_valid_singleton #t h =
  let e = non_null h.lhead in
  { h with ltail = h.lhead ; nodes = ~. e }

let g_is_singleton (#t:Type) (h:nonempty_dlisthead t) : GTot Type0 =
  g_ptr_eq (non_null h.lhead) (non_null h.ltail)

let is_singleton (#t:Type) (h:nonempty_dlisthead t) :
  ST bool
    (requires (fun h0 -> h0 `contains` (non_null h.lhead) /\ h0 `contains` (non_null h.ltail)))
    (ensures (fun h0 b h1 -> h0==h1 /\ (b <==> g_is_singleton h))) =
  ptr_eq (non_null h.lhead) (non_null h.ltail)

val nonempty_singleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ g_is_singleton h))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) == 1))
let nonempty_singleton_properties #t h = ()

val nonempty_nonsingleton_properties :
  #t:Type ->
  h:nonempty_dlisthead t ->
  ST unit
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ ~(g_is_singleton h)))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ Seq.length (reveal h.nodes) > 1))
let nonempty_nonsingleton_properties #t h = ()

val ghost_append_properties: #t:Type -> a:t -> b:erased (seq t) ->
  Lemma (let r = a ^+ b in
         forall i j. {:pattern ((reveal b).[i] == (reveal r).[j])}
           j = i + 1 /\ 0 <= i /\ i < length (reveal b) ==> (reveal b).[i] == (reveal r).[j])
let ghost_append_properties #t a b = ()

#set-options "--max_fuel 0 --max_ifuel 0"

val dlisthead_update_head: #t:eqtype -> h:nonempty_dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies_2 e (non_null h.lhead) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_head (#t:eqtype) (h:nonempty_dlisthead t) (e:gpointer (dlist t)) =
  let h1 = ST.get () in
  let n = non_null h.lhead in
  !<|= e;
  e =|> n;
  e <|= n;
  let y = { lhead = of_non_null e ; ltail = h.ltail ; nodes = e ^+ h.nodes } in
  let h2 = ST.get () in
  // let p1 (i:nat{i < Seq.length (reveal y.nodes)}) : Lemma (
  //     let nodes = reveal y.nodes in
  //     let len = length nodes in
  //     h2 `contains` nodes.[i] /\
  //     (i < len - 1 ==> nodes.[i]@h2 |> nodes.[i+1]) /\
  //     (i > 0 ==> nodes.[i-1] <| nodes.[i]@h2) /\
  //     dlist_is_valid h2 nodes.[i]
  //   ) = if i > 0 then get_all_nodes_contained h1 h (i-1) else () in
  // FStar.Classical.forall_intro p1; // Maybe this alternative style is better;
  //                                  // or maybe the latter one might give better performance
  let all_contained (i:nat{i < Seq.length (reveal y.nodes)}) : Lemma (
    let nodes = reveal y.nodes in
    h2 `contains` nodes.[i]) =
    if i > 0 then get_all_nodes_contained h1 h (i-1) else () in
  FStar.Classical.forall_intro all_contained;
  let flinks (i:nat{i < Seq.length (reveal y.nodes) - 1}) : Lemma (
    let nodes = reveal y.nodes in
    (get_all_nodes_contained h1 h i;
    nodes.[i]@h2 |> nodes.[i+1])) =
    if i > 0 then get_all_nodes_contained h1 h (i-1) else () in
  FStar.Classical.forall_intro flinks;
  let blinks (i:nat{1 <= i /\ i < Seq.length (reveal y.nodes)}) : Lemma (
    let nodes = reveal y.nodes in
    nodes.[i-1] <| nodes.[i]@h2) =
    if i > 0 then get_all_nodes_contained h1 h (i-1) else () in
  FStar.Classical.forall_intro blinks;
  let valid (i:nat{i < Seq.length (reveal y.nodes)}) : Lemma (
    let nodes = reveal y.nodes in
    dlist_is_valid h2 nodes.[i]) =
    if i > 0 then get_all_nodes_contained h1 h (i-1) else () in
  FStar.Classical.forall_intro valid;
  let dont_alias1 (i:nat{i < Seq.length (reveal y.nodes)})
                  (j:nat{j < Seq.length (reveal y.nodes)}) : Lemma (
      let nodes = reveal y.nodes in
      i < j ==>
          not_aliased (nodes.[i]@h2).flink (nodes.[j]@h2).flink) =
    (if i > 0 then get_all_nodes_contained h1 h (i-1) else ());
    (if j > 0 then get_all_nodes_contained h1 h (j-1) else ()) in
  FStar.Classical.forall_intro_2 dont_alias1;
  let dont_alias2 (i:nat{i < Seq.length (reveal y.nodes)})
                  (j:nat{j < Seq.length (reveal y.nodes)}) : Lemma (
      let nodes = reveal y.nodes in
      i < j ==>
          not_aliased (nodes.[i]@h2).blink (nodes.[j]@h2).blink) =
    (if i > 0 then get_all_nodes_contained h1 h (i-1) else ());
    (if j > 0 then get_all_nodes_contained h1 h (j-1) else ()) in
  FStar.Classical.forall_intro_2 dont_alias2;
  y

#reset-options

val insertHeadList : #t:eqtype -> h:dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 ->
         (is_not_null h.lhead ==>
          modifies_2 e (non_null h.lhead) h1 h2) /\
         (~(is_not_null h.lhead) ==>
          modifies_1 e h1 h2) /\
         dlisthead_is_valid h2 y))
let insertHeadList #t h e =
  if is_not_null h.lhead
  then dlisthead_update_head h e
  else singletonlist e

#set-options "--z3rlimit 100 --z3refresh --max_fuel 0 --max_ifuel 0"

val dlisthead_update_tail: #t:eqtype -> h:nonempty_dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 -> modifies_2 e (non_null h.ltail) h1 h2 /\ dlisthead_is_valid h2 y))
let dlisthead_update_tail #t h e =
  let previously_singleton = is_singleton h in
  let n = non_null h.ltail in
  !=|> e;
  n =|> e;
  n <|= e;
  { lhead = h.lhead ; ltail = of_non_null e ; nodes = h.nodes +^ e }

#reset-options

val insertTailList : #t:eqtype -> h:dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\ has_nothing_in h0 h e))
    (ensures (fun h1 y h2 ->
         (is_not_null h.ltail ==>
          modifies_2 e (non_null h.ltail) h1 h2) /\
         (~(is_not_null h.lhead) ==>
          modifies_1 e h1 h2) /\
         dlisthead_is_valid h2 y))
let insertTailList #t h e =
  if is_not_null h.ltail
  then dlisthead_update_tail h e
  else singletonlist e

unfold let ghost_tail (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  hide (Seq.tail (reveal s))

#set-options "--z3rlimit 100 --z3refresh --max_fuel 0 --max_ifuel 0"

val dlisthead_remove_head: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h))
    (ensures (fun h1 y h2 ->
         (g_is_singleton h ==>
          modifies_1 (non_null h.lhead) h1 h2) /\
         (~(g_is_singleton h) ==>
          modifies_2 (non_null h.lhead) (reveal h.nodes).[1] h1 h2) /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_head #t h =
  let n = non_null h.lhead in
  if is_singleton h
  then (
    empty_list
  ) else (
    let next = non_null (!n).flink in
    recall next;
    // unlink them
    !=|> n;
    !<|= next;
    { lhead = of_non_null next ; ltail = h.ltail ; nodes = ghost_tail h.nodes }
  )

#reset-options

unfold let ghost_unsnoc (#t:Type) (s:erased (seq t){Seq.length (reveal s) > 0}) : Tot (erased (seq t)) =
  let x = reveal s in
  let l = length x - 1 in
  hide (slice x 0 l)

#set-options "--z3rlimit 50 --z3refresh --max_fuel 0 --max_ifuel 0"

val dlisthead_remove_tail: #t:eqtype -> h:nonempty_dlisthead t ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h))
    (ensures (fun h1 y h2 ->
         (g_is_singleton h ==>
          modifies_1 (non_null h.ltail) h1 h2) /\
         (~(g_is_singleton h) ==>
          (let nodes = reveal h.nodes in
          modifies_2 (non_null h.ltail) nodes.[length nodes - 2] h1 h2)) /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_tail #t h =
  if is_singleton h then (
    empty_list
  ) else (
    let n = non_null h.ltail in
    let prev = non_null (!n).blink in
    recall prev;
    //unlink them
    !<|= n;
    !=|> prev;
    { lhead = h.lhead ; ltail = of_non_null prev ; nodes = ghost_unsnoc h.nodes }
  )

#reset-options

#set-options "--z3rlimit 30 --z3refresh"

// TODO: See if possible to do without the StrongExcludedMiddle
irreducible
val remove_element :
  #t:Type ->
  s:seq (gpointer t) ->
  x:ref t{s `contains_by_addr` x} ->
  GTot (res:(nat * seq (gpointer t)){
      let idx, r = res in
      (idx < length s) /\
      (length r = length s - 1) /\
      (g_ptr_eq s.[idx] x) /\
      (forall (i:nat{i < length r}). {:pattern (r.[i])} (
          ((i < idx) ==> s.[i] == r.[i]) /\
          ((i >= idx) ==> s.[i+1] == r.[i])))})
    (decreases (length s))
let rec remove_element #t s x =
  contains_elim s x;
  let h, t = Seq.head s, Seq.tail s in
  if StrongExcludedMiddle.strong_excluded_middle (g_ptr_eq h x) then 0, t else (
    contains_cons h t x;
    let idx, r = remove_element t x in
    idx + 1, Seq.cons h r)

// See https://github.com/FStarLang/FStar/pull/1428
// Most probably this assumption will become part of ulib
assume
val elift2_pq : #a:Type
              -> #c:Type
              -> #p: (a -> c -> Type)
              -> #b:Type
              -> #q: (xa:a -> xc:c{p xa xc} -> b -> Type)
              -> $f:(xa:a -> xc:c{p xa xc} -> GTot (y:b{q xa xc y}))
              -> ra:erased a
              -> rc:erased c{p (reveal ra) (reveal rc)}
              -> Tot (x:erased b{reveal x == f (reveal ra) (reveal rc)})

// // Needed if we don't get elift2_pq in
// let remove_element (#t:Type) (s:seq (gpointer t)) (x:ref t{s `contains_by_addr` x})
//   : GTot (idx:nat * r:seq (gpointer t)) = remove_element_aux s x
// val remove_element_lemma:
//   #t:Type ->
//   s:seq (gpointer t) ->
//   x:ref t{s `contains_by_addr` x} ->
//   Lemma (
//     let res = remove_element s x in
//     let idx, r = res in
//     (idx < length s) /\
//     (length r = length s - 1) /\
//     (g_ptr_eq s.[idx] x) /\
//     (forall (i:nat{i < length r}). {:pattern (r.[i])} (
//         ((i < idx) ==> s.[i] == r.[i]) /\
//         ((i >= idx) ==> s.[i+1] == r.[i]))))
//         [SMTPat (remove_element s x)]
// let remove_element_lemma #t s x = ()

#reset-options "--z3rlimit 1 --detail_errors --z3rlimit_factor 100 --max_fuel 0 --max_ifuel 0"

val dlisthead_remove_strictly_mid: #t:eqtype -> h:nonempty_dlisthead t -> e:gpointer (dlist t) ->
  ST (dlisthead t)
    (requires (fun h0 -> dlisthead_is_valid h0 h /\ dlist_is_valid h0 e /\
                         member_of h0 h e /\
                         not_aliased0 e h.lhead /\ not_aliased0 e h.ltail))
    (ensures (fun h1 y h2 ->
         is_not_null (e@h1).flink /\ is_not_null (e@h1).blink /\
         dlist_is_valid h2 e /\
         modifies_2 (non_null (e@h1).flink) (non_null (e@h1).blink) h1 h2 /\
         dlisthead_is_valid h2 y))
let dlisthead_remove_strictly_mid #t h e =
  let h1 = ST.get () in
  let prev = non_null (!e).blink in
  let next = non_null (!e).flink in
  lemma_all_elements_distinct (ST.get ()) h; // required to be able to say [prev]
                                             //     and [next] are not same
  recall prev;
  recall next;
  prev =|> next;
  prev <|= next;
  let nodes' = elift2_pq remove_element h.nodes (Ghost.hide e) in
  let idx, nodes = elift1 fst nodes', elift1 snd nodes' in
  let y = { lhead = h.lhead ; ltail = h.ltail ; nodes = nodes } in
  let h2 = ST.get () in
  // assert (
  //   let ynodes = reveal y.nodes in
  //   let hnodes = reveal h.nodes in
  //   (forall (i:nat{0 <= i /\ i < reveal idx - 1}).
  //      i < length ynodes /\
  //      i < length hnodes /\
  //      ynodes.[i]@h2 == hnodes.[i]@h1 /\
  //      True
  //      )); // OBSERVE
  // assert (
  //   let h0, h = h2, y in
  //   let nodes = reveal h.nodes in
  //   let len = length nodes in
  //   let loc = reveal idx in
  //   (forall i. {:pattern ((nodes.[i]@h0).flink)}
  //      ((0 <= i /\ i < loc - 2) ==>
  //       nodes.[i]@h0 |> nodes.[i+1])) /\
  //   True
  // );
  assume (flink_valid h2 y);
  assume (blink_valid h2 y);
  // admit () //;
  y

/// Useful code that can be copied over below

(*
    assert (all_nodes_contained h2 y);
    assert (dlisthead_ghostly_connections h2 y);
    assert (flink_valid h2 y);
    assert (blink_valid h2 y);
    assert (elements_are_valid h2 y);
    assert (elements_dont_alias1 h2 y);
    assert (elements_dont_alias2 h2 y);
    // assert (all_elements_distinct h2 y);
*)
