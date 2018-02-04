module CBS

open FStar
open FStar.Seq
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Mul

open CBS.Spec

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module ST = FStar.HyperStack.ST

#reset-options "--max_fuel 5 --z3rlimit 100"

private
let uint8_p : Type0 = b:buffer U8.t{length b < pow2 32}

// typedef struct {
//   uint8_t *data;
//   uint32_t len;
// } cbs_t;
private noeq
type cbs_t = | MkCBS: (* {data:buffer U8.t; len:U32.t} *)
  data: uint8_p ->
  len: U32.t{U32.v len == length data} ->
  cbs_t

private inline_for_extraction
let u8_to_u32 n = FStar.Int.Cast.uint8_to_uint32 n

private inline_for_extraction
let u32_to_u16 n = FStar.Int.Cast.uint32_to_uint16 n


// bool cbs_skip(cbs_t *cbs, uint32_t num)
val cbs_skip :
  cbs: buffer cbs_t{length cbs = 1} ->
  num: U32.t{U32.v num < pow2 32} ->
  ST bool
  (requires (fun h -> live h cbs))
  (ensures (fun h0 r h1 -> modifies_1 cbs h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == U32.(v cbs0.len >= v num) /\
      // Ensure the result is a subset of the original area.
      (r ==> includes cbs0.data (get h1 cbs 0).data) /\
      // Ensure that the length was reduced by `num` bytes.
      (r ==> length (get h1 cbs 0).data == U32.(v cbs0.len - v num)) /\
      // Ensure we actually skipped `num` bytes.
      (r ==> idx cbs0.data + U32.v num == idx (get h1 cbs 0).data)
    )
  ))

let cbs_skip cbs num =
  let cbs0 = cbs.(0ul) in
  let len = cbs0.len in
  if U32.(len >=^ num) then (
    cbs.(0ul) <- MkCBS (offset cbs0.data num) U32.(len -^ num);
    let cbs0' = cbs.(0ul) in assert U32.(cbs0.len == cbs0'.len +^ num);
    true
  ) else (
    false
  )


// bool cbs_get(cbs_t *cbs, uint8_t **out, uint32_t num)
val cbs_get :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer uint8_p{length out = 1} ->
  num: U32.t{U32.v num < pow2 32} ->
  ST bool
  (requires (fun h -> live h cbs /\ live h out /\ disjoint cbs out))
  (ensures (fun h0 r h1 -> modifies_2 cbs out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == U32.(v cbs0.len >= v num) /\
      // Ensure `out` is a subset of the original area.
      (r ==> includes cbs0.data (get h1 out 0)) /\
      // Ensure that `out` is of length `num` bytes.
      (r ==> length (get h1 out 0) == U32.v num) /\
      // Ensure `cbs->data` == `*out`.
      (r ==> idx cbs0.data == idx (get h1 out 0)) /\
      // Ensure we skipped `num` bytes.
      (r ==> idx (get h1 cbs 0).data == idx (get h1 out 0) + U32.v num)
    )
  ))

let cbs_get cbs out num =
  let cbs0 = cbs.(0ul) in
  let len = cbs0.len in
  if U32.(len >=^ num) then (
    out.(0ul) <- sub cbs0.data 0ul num;
    cbs_skip cbs num
  ) else (
    false
  )


// Generic pre-conditions for `cbs_get_u*` functions.
[@ "substitute"] private
let cbs_out_precond cbs out = fun h ->
  // `cbs` and `out` should be normal pointers.
  length cbs = 1 /\ length out = 1 /\ (let data = (get h cbs 0).data in (
    // Ensure that `cbs_t *cbs`, `cbs->data`, and `uintX_t *out` are live.
    live h cbs /\ live h data /\ live h out /\
    // Ensure that none of the above memory areas intersect.
    disjoint cbs out /\ disjoint out data /\ disjoint cbs data
  ))


// bool cbs_get_u(cbs_t *cbs, uint32_t *out, uint32_t num)
val cbs_get_u :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  num: U32.t{U32.v num < pow2 32} ->
  ST bool
  (requires (cbs_out_precond cbs out))
  (ensures (fun h0 r h1 -> live h0 out /\ live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes, or num is out of range.
      r == U32.(v cbs0.len >= v num && v num > 0 && v num < 5) /\
      // The result must be < 2^(num * 8).
      (r ==> U32.v (get h1 out 0) < pow2 (U32.v num * 8)) /\
      // If there are, check the result.
      (r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 (U32.v num)))
    )))

let cbs_get_u cbs out num =
  let cbs0 = cbs.(0ul) in
  let h0 = ST.get() in
  // Check that `num` is in the allowed range.
  if U32.(num >^ 0ul && num <^ 5ul && cbs0.len >=^ num) then (
    let inv = (fun h i -> live h out /\ live h cbs0.data /\ modifies_1 out h0 h /\
      0 <= i /\ i <= U32.v num /\
      // Current value must be < 2^(i * 8).
      U32.v (get h out 0) < pow2 (i * 8) /\
      // Current value must agree with `big_endian` result.
      U32.v (get h out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 i)
    ) in
    let f (i:U32.t{U32.(v 0ul <= v i /\ v i < v num)}) :
      Stack unit
        (requires (fun h -> inv h (U32.v i)))
        (ensures (fun h0 _ h1 -> inv h1 (U32.v i + 1)))
      = let bi = cbs0.data.(i) in
        let lo = u8_to_u32 bi in
        Math.Lemmas.pow2_plus 8 8;
        Math.Lemmas.pow2_plus 8 16;
        Math.Lemmas.pow2_plus 8 24;
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
  out: uint8_p{length out = 1} ->
  ST bool
  (requires (cbs_out_precond cbs out))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_2 cbs out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 0) /\
      // If there are, the result will be cbs->data[0].
      (r ==> U8.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 1)) /\
      // Ensure the result is a subset of the original area.
      (r ==> includes cbs0.data (get h1 cbs 0).data) /\
      // Ensure that the length was reduced by `num` bytes.
      (r ==> length (get h1 cbs 0).data == U32.v cbs0.len - 1) /\
      // Ensure we skipped a byte.
      (r ==> idx cbs0.data + 1 == idx (get h1 cbs 0).data)
    )))

let cbs_get_u8 cbs out =
  let cbs0 = cbs.(0ul) in
  if U32.(cbs0.len >^ 0ul) then (
    out.(0ul) <- cbs0.data.(0ul);
    cbs_skip cbs 1ul
  ) else (
    false
  )


// bool cbs_get_u16(cbs_t *cbs, uint16_t *out)
val cbs_get_u16 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U16.t{length out = 1} ->
  ST bool
  (requires (cbs_out_precond cbs out))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 1) /\
      // If there are, check the result.
      (r ==> U16.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 2))
    )))

let cbs_get_u16 cbs out =
  (**) push_frame ();
  let num = createL [ 0ul ] in
  let rv = cbs_get_u cbs num 2ul in
  let num0 = num.(0ul) in
  out.(0ul) <- u32_to_u16 num0;
  (**) pop_frame ();
  rv


// bool cbs_get_u24(cbs_t *cbs, uint32_t *out)
val cbs_get_u24 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  ST bool
  (requires (cbs_out_precond cbs out))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 2) /\
      // If there are, check the result.
      (r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 3)) /\
      // The result must be < 2^24.
      (r ==> U32.v (get h1 out 0) < pow2 24)
    )))

let cbs_get_u24 cbs out =
  cbs_get_u cbs out 3ul


// bool cbs_get_u32(cbs_t *cbs, uint32_t *out)
val cbs_get_u32 :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  ST bool
  (requires (cbs_out_precond cbs out))
  (ensures (fun h0 r h1 -> live h1 out /\ modifies_1 out h0 h1 /\
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == (U32.v cbs0.len > 3) /\
      // If there are, check the result.
      (r ==> U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 4))
    )))

let cbs_get_u32 cbs out =
  cbs_get_u cbs out 4ul
