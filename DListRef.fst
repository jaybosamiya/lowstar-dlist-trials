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
  nodes: erased (seq (dlist t));
}

(** Initialize an element of a doubly linked list *)
let empty_entry (#t:Type) (payload:t) : dlist t =
  { flink = None ; blink = None ; p = payload }

(** Initialize a doubly linked list head *)
let empty_list (#t:Type) : dlisthead t =
  { lhead = None ; ltail = None ; nodes = hide createEmpty }

let getSome (a : option 't{isSome a}) =
  match a with
  | Some x -> x

let (@) (a:ref 't) (h0:heap) = sel h0 a
let (^@) (a:option (ref 't){isSome a}) (h0:heap) = (getSome a) @ h0

let (.[]) (s:seq 'a) (n:nat{n < length s}) = index s n

let dlisthead_is_valid (#t:Type) (h0:heap) (h:dlisthead t) =
  let nodes = reveal h.nodes in
  let len = length nodes in
  let empty = (len = 0) in
  (empty ==> isNone h.lhead /\ isNone h.ltail) /\
  (~empty ==> (isSome h.lhead /\ isSome h.ltail) /\
              isNone (h.lhead^@h0).blink /\
              isNone (h.ltail^@h0).flink /\
              h.lhead^@h0 == nodes.[0] /\
              h.ltail^@h0 == nodes.[len-1] /\
              (forall i. {:pattern (nodes.[i]).blink}
                 ((1 <= i /\ i < len) ==>
                  isSome (nodes.[i]).blink /\
                  (nodes.[i]).blink^@h0 == nodes.[i-1])) /\
              (forall i. {:pattern (nodes.[i]).flink}
                 ((0 <= i /\ i < len - 1) ==>
                  isSome (nodes.[i]).flink /\
                  (nodes.[i]).flink^@h0 == nodes.[i+1])))

let test1 () = assert (forall h0 t. dlisthead_is_valid h0 (empty_list #t))

let singletonlist (#t:eqtype) (e:ref (dlist t)) =
  e := { !e with blink = None; flink = None };
  { lhead = Some e ; ltail = Some e ; nodes = hide (Seq.create 1 (!e)) }

let insertHeadList (#t:eqtype) (h:dlisthead t) (e:ref (dlist t)): ST (dlisthead t)
   (requires (fun h0 -> dlisthead_is_valid h0 h))
   (ensures (fun _ y h2 -> dlisthead_is_valid h2 y)) =
  if isNone h.lhead
  then (
    singletonlist e
  ) else (
    empty_list // TODO: Remove. temporary kludge
  )

