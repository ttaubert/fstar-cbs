module CBS

open FStar
open FStar.Seq
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Mul

module ST = FStar.HyperStack.ST

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

#reset-options "--max_fuel 5 --z3rlimit 100"

private
noeq type cbs_t = | MkCBS: data:(buffer U8.t) -> len:U32.t{U32.v len == length data} -> cbs_t

[@ "substitute"] private
let u8_to_u32 n = FStar.Int.Cast.uint8_to_uint32 n

[@ "substitute"] private
let u32_to_u16 n = FStar.Int.Cast.uint32_to_uint16 n

private // TODO move to CBS.Spec ?
let rec big_endian (b:seq U8.t) : Tot (n:nat) (decreases (Seq.length b)) =
  let open FStar.Seq in
    if length b = 0 then 0
    else U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))

val cbs_get_u :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  num: U32.t{U32.(v num > 0 /\ v num < 5)} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data))
  (ensures (fun h0 r h1 -> live h0 out /\ live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == U32.(v cbs0.len >= v num) //\
      // If there are, check the result.
      //(r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 (U32.v num)))
    )))

let cbs_get_u cbs out num =
  let cbs0 = cbs.(0ul) in
  let h0 = ST.get() in
  if U32.(cbs0.len >=^ num) then (
    let inv = (fun h _ -> live h out /\ live h cbs0.data /\ modifies_1 out h0 h) in
    let f (i:U32.t{U32.(v 0ul <= v i /\ v i < v num)}) :
      Stack unit
        (requires (fun h -> live h out /\ live h cbs0.data))
        (ensures (fun h0 _ h1 -> modifies_1 out h0 h1))
      = let bi = cbs0.data.(i) in
        out.(0ul) <- U32.((out.(0ul) <<^ 8ul) |^ u8_to_u32 bi)
    in
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
      (r ==> U8.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 1))
    )))

let cbs_get_u8 cbs out =
  let cbs0 = cbs.(0ul) in
  if U32.(cbs0.len >^ 0ul) then (
    out.(0ul) <- cbs0.data.(0ul);
    true
  ) else (
    false
  )

val cbs_get_u16 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U16.t{length out = 1} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 1) //\
      // If there are, check the result.
      //(r ==> U16.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 2))
    )))

let cbs_get_u16 cbs out =
  push_frame ();
  let num = Buffer.createL [ 0ul ] in
  let rv = cbs_get_u cbs num 2ul in
  let num0 = num.(0ul) in
  out.(0ul) <- u32_to_u16 num0;
  pop_frame ();
  rv

val cbs_get_u24 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 2) //\
      // If there are, check the result.
      //(r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 3))
    )))

let cbs_get_u24 cbs out =
  cbs_get_u cbs out 3ul

val cbs_get_u32 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 3) //\
      // If there are, check the result.
      //(r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 4))
    )))

let cbs_get_u32 cbs out =
  cbs_get_u cbs out 4ul
