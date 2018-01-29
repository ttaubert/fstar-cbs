module CBS

open FStar
open FStar.Seq
open FStar.HyperStack.ST
open FStar.Buffer

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
//module HST = FStar.HyperStack.ST

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

noeq type cbs_t = | MkCBS: data:(buffer U8.t) -> len:U32.t{U32.v len == length data} -> cbs_t

[@ "substitute"] private
let u8_to_u32 n = FStar.Int.Cast.uint8_to_uint32 n

[@ "substitute"] private
let u32_to_u16 n = FStar.Int.Cast.uint32_to_uint16 n

val cbs_get_u :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  num: U32.t{U32.(v num > 0 /\ v num < 5)} ->
  ST bool
  (requires (fun h -> live h cbs /\ live h out /\ live h (get h cbs 0).data))
  (ensures (fun h0 _ h1 -> live h1 out)) // /\ modifies_1 out h0 h1)) // TODO

let cbs_get_u cbs out num =
  let cbs0 = cbs.(0ul) in
  if U32.(cbs0.len >=^ num) then (
    //let h0 = HST.get () in
    //let cbs0 = (Seq.index (as_seq h0 cbs) 0).data in
    //let inv h1 i = (
      //let cur = Seq.index (as_seq h0 cbs0) i in
      //let cur = get h1 (get h1 cbs 0).data i in
      //let res = get h1 out 0 in
      //let res = Seq.index (as_seq h1 out) 0 in
      //U32.(res =^ ((Seq.index (as_seq h0 out) 0) <<^ 8ul) +^ u8_to_u32 cur))
      (*forall j. 0 <= j /\ j < i ==> (
        let old = Seq.index (as_seq h0 cbs0) j in
        let new_ = Seq.index (as_seq h1 out) 0 in
        U32.(new_ =^ (old <<^ 8ul) +^ u8_to_u32 (Seq.index (as_seq h0 out) 0)))
      *)
    //in
    let inv = (fun h _ -> live h out) in
    //let inv = (fun h _ -> live h cbs /\ live h out /\ live h (get h cbs 0).data) in
    //let inv = (fun h i -> live h cbs /\ live h (get h cbs 0).data /\ live h out /\ length (get h cbs 0).data >= i) in
    //let f (i:U32.t{U32.(v i < v num /\ v i < length cbs0.data /\ 0 <= v i)}) :
    let f (i:U32.t{U32.(v 0ul <= v i /\ v i < v num)}) :
      Stack unit
        //(requires (fun h -> inv h (UInt32.v i)))
        //(ensures (fun h0 r h1 -> inv h0 i /\ inv h1 i))
        //(fun h -> live h cbs /\ live h out /\ live h (get h cbs 0).data /\ 0 <= U32.v i /\ length (get h cbs 0).data > U32.v i)
        (fun h -> live h out)
        //(fun h0 _ h1 -> live h1 cbs /\ live h1 (get h1 cbs 0).data /\ live h1 out /\ modifies_1 out h0 h1)
        (fun h0 _ h1 -> true) // TODO modifies
      //= let bi = cbs0.data.(i) in
        //out.(0ul) <- U32.((out.(0ul) <<^ 8ul) +^ u8_to_u32 bi) in
      = out.(0ul) <- 0ul;
        () in
    //assert (length cbs0.data >= U32.v num);
    //assert U32.(cbs0.len >=^ num);
    //assert U32.(0 < v num /\ v num <= 4);
    C.Loops.for 0ul num inv f;
    true
  ) else (
    false
  )

val cbs_get_u8 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U8.t{length out = 1} ->
  ST bool
  (requires (fun h -> live h cbs /\ live h out /\ live h (get h cbs 0).data))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 0) /\
      // If there are, the result will be cbs->data[0].
      (not(r) \/ get h1 out 0 == get h0 cbs0.data 0)
    )))

let cbs_get_u8 cbs out =
  let cbs0 = cbs.(0ul) in
  if U32.(cbs0.len >^ 0ul) then (
    out.(0ul) <- cbs0.data.(0ul);
    true
  ) else (
    false
  )

(*
val cbs_get_u16 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U16.t{length out = 1} ->
  ST bool
  (fun _ -> true)
  (fun _ _ _ -> true)

let cbs_get_u16 cbs out =
  push_frame ();
  let num = Buffer.createL [ 0ul ] in
  let rv = if cbs_get_u cbs num 2ul then (
    let num0 = num.(0ul) in
    out.(0ul) <- u32_to_u16 num0;
    true
  ) else (
    false
  ) in
  pop_frame();
  rv

val cbs_get_u24 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  ST bool
  (fun _ -> true)
  (fun _ _ _ -> true)

let cbs_get_u24 cbs out =
  cbs_get_u cbs out 3ul

val cbs_get_u32 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  ST bool
  (fun _ -> true)
  (fun _ _ _ -> true)

let cbs_get_u32 cbs out =
  cbs_get_u cbs out 4ul
*)
