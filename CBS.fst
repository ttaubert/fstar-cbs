module CBS

open FStar
open FStar.Seq
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Mul
//open FStar.Kremlin.Endianness

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32

//#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"
#reset-options "--max_fuel 5 --z3rlimit 100"

private
noeq type cbs_t = | MkCBS: data:(buffer U8.t) -> len:U32.t{U32.v len == length data} -> cbs_t

[@ "substitute"] private
let u8_to_u32 n = FStar.Int.Cast.uint8_to_uint32 n

[@ "substitute"] private
let u32_to_u16 n = FStar.Int.Cast.uint32_to_uint16 n

// TODO move to CBS.Spec
private
let rec big_endian (b:seq U8.t) : Tot (n:nat) (decreases (Seq.length b)) =
  let open FStar.Seq in
    if length b = 0 then 0
    else U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))

(*
private
val big_endian_single: n:U8.t -> Lemma
  (ensures (big_endian (Seq.create 1 n) = U8.v n))
  [SMTPat (big_endian (Seq.create 1 n) = U8.v n)]
let big_endian_single n =
  let open FStar.Seq in
  let s = (create 1 n) in
  assert (big_endian s = U8.v (index s 0) + pow2 8 * big_endian (slice s 0 0));
  assert (U8.v (index s 0) > 0 ==> big_endian s > 0);
  assert (big_endian s > 0 ==> U8.v (index s 0) > 0);
  assert (U8.v (index s 0) = 0 ==> big_endian s = 0);
  assert (big_endian s = 0 ==> U8.v (index s 0) = 0);
  ()
*)

private
let lemma_uint32s_from_le_def_0 (b:seq U8.t{Seq.length b == 0}) : Lemma
  (big_endian b == 0)
= ()

val cbs_get_u :
  cbs: buffer cbs_t{length cbs = 1} ->
  out: buffer U32.t{length out = 1} ->
  num: U32.t{U32.(v num > 0 /\ v num < 5)} ->
  ST bool
  (requires (fun h -> live h out /\ live h cbs /\ live h (get h cbs 0).data))
  (ensures (fun h0 r h1 -> live h1 out /\ // modifies_1 out h0 h1 ?
    (let cbs0 = get h0 cbs 0 in
      // Return false if there aren't enough bytes.
      r == U32.(v cbs0.len >= v num) //\
      // If there are, check the result.
      //(not(r) \/ U32.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 (U32.v num)))
      //(not(r) \/ U32.v (get h1 out 0) == be_to_n (as_seq h0 cbs0.data))
      //(not(r) \/ U32.v (get h1 out 0) == be_to_n (slice (as_seq h0 cbs0.data) 0 (U32.v num)))
    )))

let cbs_get_u cbs out num =
  //out.(0ul) <- 0ul;
  let cbs0 = cbs.(0ul) in
  if U32.(cbs0.len >=^ num) then (
    let inv = (fun h _ -> live h out /\ live h cbs0.data
      ///\ U32.v (get h out 0) == big_endian (slice (as_seq h cbs0.data) 0 i)) in
      ///\ U32.v (get h out 0) == be_to_n (slice (as_seq h cbs0.data) 0 i)
      ///\ Seq.length (slice (as_seq h cbs0.data) 0 0) == 0
      ///\ be_to_n (Seq.create 0 0uy) == 0
      ///\ big_endian (Seq.create 0 0uy) == 0
      ///\ big_endian (slice (as_seq h cbs0.data) 0 0) == 0
      ///\ big_endian (slice (as_seq h cbs0.data) 0 0) == 0
    ) in
    let f (i:U32.t{U32.(v 0ul <= v i /\ v i < v num)}) :
      Stack unit
        (requires (fun h -> live h out /\ live h cbs0.data))
        (ensures (fun h0 _ h1 -> modifies_1 out h0 h1))
      = let bi = cbs0.data.(i) in
        let lo = u8_to_u32 bi in
      //Math.Lemmas.pow2_lt_compat 32 8; // TODO
      //cut (U32.v lo = U8.v bi); // TODO
      //Math.Lemmas.pow2_lt_compat 16 8;
      //Math.Lemmas.pow2_lt_compat 24 16;
      //Math.Lemmas.pow2_lt_compat 32 24;
      //Math.Lemmas.pow2_plus 8 8;
      //Math.Lemmas.pow2_plus 8 16;
      //Math.Lemmas.pow2_plus 8 24;
        let hi = U32.(out.(0ul) <<^ 8ul) in
      //UInt.shift_left_value_lemma #32 (U32.v out.(0ul)) 8;
      //Math.Lemmas.modulo_lemma (U32.v out.(0ul)) (pow2 32);
      //Math.Lemmas.modulo_lemma (U32.v hi) (pow2 32); // TODO
      //cut (U32.v hi == (pow2 8) * (U32.v out.(0ul)));
        let res = U32.(hi |^ lo) in
      //UInt.logor_disjoint #32 (U32.v hi) (U32.v lo) 8;
      //assert (U32.v res == (U32.v hi) + (U32.v lo));
      //assert U32.(v res == v lo + v out.(0ul) * (pow2 8)); // TODO
        out.(0ul) <- res
    in
    C.Loops.for 0ul num inv f;
    //let h = FStar.HyperStack.ST.get () in
    //assert (U32.v out.(0ul) == big_endian (slice (as_seq h cbs0.data) 0 (U32.v num)));
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
      //(not(r) \/ get h1 out 0 == get h0 cbs0.data 0) // TODO
      (not(r) \/ U8.v (get h1 out 0) == big_endian (slice (as_seq h0 cbs0.data) 0 1))
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
