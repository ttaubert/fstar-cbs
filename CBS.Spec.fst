module CBS.Spec

open FStar.Seq
open FStar.Mul

module U8 = FStar.UInt8


private
val pow2_0_lemma: n:nat ->
  Lemma
    (requires (n = 0))
    (ensures  (pow2 n = 1))
    [SMTPat (pow2 n)]
let pow2_0_lemma n = assert_norm(pow2 0 = 1)

private
val pow2_8_lemma: n:nat ->
  Lemma
    (requires (n = 8))
    (ensures  (pow2 n = 256))
    [SMTPat (pow2 n)]
let pow2_8_lemma n = assert_norm(pow2 8 = 256)


let rec big_endian (b:seq U8.t) : Tot (n:nat) (decreases (Seq.length b)) =
  if length b = 0 then 0
  else U8.v (last b) + pow2 8 * big_endian (slice b 0 (length b - 1))


private
val big_endian_zero: (b:seq U8.t) -> Lemma
  (ensures (big_endian (slice b 0 0) = 0))
  [SMTPat (big_endian (slice b 0 0))]
let big_endian_zero b = ()
