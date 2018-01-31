module CBS

open FStar
open FStar.Seq
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Mul

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

#reset-options "--max_fuel 5 --z3rlimit 100"

private
noeq type cbs_t = | MkCBS: data:(buffer U8.t) -> len:U32.t{U32.v len == length data} -> cbs_t

[@ "substitute"] private
let u8_to_u32 n = FStar.Int.Cast.uint8_to_uint32 n

[@ "substitute"] private
let u32_to_u16 n = FStar.Int.Cast.uint32_to_uint16 n


// TODO get rid of seq.last
private // TODO move to CBS.Spec ?
let rec big_endian (b:seq U8.t) : Tot (n:nat) (decreases (Seq.length b)) =
  let open FStar.Seq in
    if length b = 0 then 0
    else U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))


// bool cbs_get_u(cbs_t *cbs, uint32_t *out, uint32_t num)
// TODO check that num < 5
val cbs_get_u :
  cbs: buffer cbs_t{length cbs = 1} -> // TODO cbs_p ?
  out: buffer U32.t{length out = 1 /\ disjoint out cbs} -> // TODO uint32_p ?
  num: U32.t{U32.(v num > 0 /\ v num < 5)} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data
    /\ disjoint out (get h cbs 0).data /\ disjoint cbs (get h cbs 0).data // TODO
  ))
  (ensures (fun h0 r h1 -> live h0 out /\ live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == U32.(v cbs0.len >= v num) /\
      // If there are, check the result.
      (r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 (U32.v num))) // TODO
    )))

let cbs_get_u cbs out num =
  let cbs0 = cbs.(0ul) in
  let h0 = ST.get() in
  if U32.(cbs0.len >=^ num) then (
    let inv = (fun h i -> live h out /\ live h cbs0.data /\ modifies_1 out h0 h
      /\ 0 <= i /\ i <= U32.v num // TODO comments
      /\ U32.v (get h out 0) < pow2 (i * 8)
      /\ U32.v (get h out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 i)
    ) in
    let f (i:U32.t{U32.(v 0ul <= v i /\ v i < v num)}) :
      Stack unit
        (requires (fun h -> inv h (U32.v i)))
        (ensures (fun h0 _ h1 -> inv h1 (U32.v i + 1)))
      = let bi = cbs0.data.(i) in
        let lo = u8_to_u32 bi in
        Math.Lemmas.pow2_plus 8 8;
        Math.Lemmas.pow2_plus 8 16;
        let hi = U32.(out.(0ul) <<^ 8ul) in
        UInt.logor_disjoint #32 (U32.v hi) (U32.v lo) 8;
        out.(0ul) <- U32.(hi |^ lo)
    in
    out.(0ul) <- 0ul;
    C.Loops.for 0ul num inv f;
    true
  ) else (
    false
  )


// bool cbs_get_u8(cbs_t *cbs, uint8_t *out)
val cbs_get_u8 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U8.t{length out = 1 /\ disjoint out cbs} ->
  ST bool
  (requires (fun h -> live h cbs /\ live h out /\ live h (get h cbs 0).data
    /\ disjoint out (get h cbs 0).data /\ disjoint cbs (get h cbs 0).data
  ))
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


// bool cbs_get_u16(cbs_t *cbs, uint16_t *out)
val cbs_get_u16 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U16.t{length out = 1 /\ disjoint out cbs} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data
    /\ disjoint out (get h cbs 0).data /\ disjoint cbs (get h cbs 0).data
  ))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 1) /\
      // If there are, check the result.
      (r ==> U16.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 2))
    )))

let cbs_get_u16 cbs out =
  push_frame ();
  let num = Buffer.createL [ 0ul ] in
  let rv = cbs_get_u cbs num 2ul in
  let num0 = num.(0ul) in
  out.(0ul) <- u32_to_u16 num0;
  pop_frame ();
  rv


// bool cbs_get_u24(cbs_t *cbs, uint32_t *out)
// TODO check that it's always < pow2 24
val cbs_get_u24 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1 /\ disjoint out cbs} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data
    /\ disjoint out (get h cbs 0).data /\ disjoint cbs (get h cbs 0).data
  ))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 2) /\
      // If there are, check the result.
      (r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 3))
    )))

let cbs_get_u24 cbs out =
  cbs_get_u cbs out 3ul


// bool cbs_get_u32(cbs_t *cbs, uint32_t *out)
val cbs_get_u32 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1 /\ disjoint out cbs} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data
    /\ disjoint out (get h cbs 0).data /\ disjoint cbs (get h cbs 0).data
  ))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 3) /\
      // If there are, check the result.
      (r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 4))
    )))

let cbs_get_u32 cbs out =
  cbs_get_u cbs out 4ul
