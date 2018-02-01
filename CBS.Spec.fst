module CBS.Spec

open FStar.Seq
open FStar.Mul

module U8 = FStar.UInt8


// Speed up verification a bit.
private
val pow2_0_lemma: n:nat ->
  Lemma
    (requires (n = 0))
    (ensures  (pow2 n = 1))
    [SMTPat (pow2 n)]
let pow2_0_lemma n = assert_norm(pow2 0 = 1)

// Speed up verification a bit.
private
val pow2_8_lemma: n:nat ->
  Lemma
    (requires (n = 8))
    (ensures  (pow2 n = 256))
    [SMTPat (pow2 n)]
let pow2_8_lemma n = assert_norm(pow2 8 = 256)


// Parse a given sequence of bytes in big-endian form, return a number.
let rec big_endian (b:seq U8.t) : Tot (n:nat) (decreases (length b)) =
  if length b = 0 then 0
  else U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))


// Speed up verification a bit.
private
val lemma_big_endian_0: (b:seq U8.t) -> Lemma
  (ensures (big_endian (slice b 0 0) = 0))
  [SMTPat (big_endian (slice b 0 0))]
let lemma_big_endian_0 b = ()


// Ensure that big_endian always returns a number
// smaller than 2^(n*8) for a sequence of length n.
private
val lemma_big_endian_bounds: (b:seq U8.t) -> Lemma
  (ensures (big_endian b < pow2 (length b * 8)))
  (decreases (length b))
  [SMTPat (big_endian b < pow2 (length b * 8))]
let rec lemma_big_endian_bounds b =
  let len = length b in
    if len > 0 then (
      lemma_big_endian_bounds (slice b 0 (len - 1));
      Math.Lemmas.pow2_minus (len * 8) ((len - 1) * 8);
      ()
    )
