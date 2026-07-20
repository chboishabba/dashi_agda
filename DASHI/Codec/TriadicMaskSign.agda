module DASHI.Codec.TriadicMaskSign where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Exact finite carriers.
------------------------------------------------------------------------

data Trit : Set where
  neg zero pos : Trit

data Bit : Set where
  off on : Bit

data Sign : Set where
  minus plus : Sign

data Unit : Set where
  unit : Unit

ActiveSign : Bit → Set
ActiveSign off = Unit
ActiveSign on  = Sign

record TritCode : Set where
  constructor code
  field
    active : Bit
    sign   : ActiveSign active

open TritCode public

encodeTrit : Trit → TritCode
encodeTrit neg  = code on minus
encodeTrit zero = code off unit
encodeTrit pos  = code on plus

decodeTrit : TritCode → Trit
decodeTrit (code off unit) = zero
decodeTrit (code on minus) = neg
decodeTrit (code on plus)  = pos

decode-encode-trit : ∀ t → decodeTrit (encodeTrit t) ≡ t
decode-encode-trit neg  = refl
decode-encode-trit zero = refl
decode-encode-trit pos  = refl

encode-decode-trit : ∀ c → encodeTrit (decodeTrit c) ≡ c
encode-decode-trit (code off unit) = refl
encode-decode-trit (code on minus) = refl
encode-decode-trit (code on plus)  = refl

------------------------------------------------------------------------
-- Three balanced trits: 27 states as one 3-bit support mask plus
-- exactly one gated sign for every active coordinate.
------------------------------------------------------------------------

record Trit3 : Set where
  constructor tri3
  field
    x y z : Trit

open Trit3 public

record Mask3 : Set where
  constructor mask3
  field
    mx my mz : Bit

open Mask3 public

record MaskSign3 : Set where
  constructor maskSign3
  field
    mask : Mask3
    sx   : ActiveSign (mx mask)
    sy   : ActiveSign (my mask)
    sz   : ActiveSign (mz mask)

open MaskSign3 public

encode3 : Trit3 → MaskSign3
encode3 (tri3 neg  neg  neg)  = maskSign3 (mask3 on  on  on)  minus minus minus
encode3 (tri3 neg  neg  zero) = maskSign3 (mask3 on  on  off) minus minus unit
encode3 (tri3 neg  neg  pos)  = maskSign3 (mask3 on  on  on)  minus minus plus
encode3 (tri3 neg  zero neg)  = maskSign3 (mask3 on  off on)   minus unit  minus
encode3 (tri3 neg  zero zero) = maskSign3 (mask3 on  off off)  minus unit  unit
encode3 (tri3 neg  zero pos)  = maskSign3 (mask3 on  off on)   minus unit  plus
encode3 (tri3 neg  pos  neg)  = maskSign3 (mask3 on  on  on)   minus plus  minus
encode3 (tri3 neg  pos  zero) = maskSign3 (mask3 on  on  off)  minus plus  unit
encode3 (tri3 neg  pos  pos)  = maskSign3 (mask3 on  on  on)   minus plus  plus
encode3 (tri3 zero neg  neg)  = maskSign3 (mask3 off on  on)   unit  minus minus
encode3 (tri3 zero neg  zero) = maskSign3 (mask3 off on  off)  unit  minus unit
encode3 (tri3 zero neg  pos)  = maskSign3 (mask3 off on  on)   unit  minus plus
encode3 (tri3 zero zero neg)  = maskSign3 (mask3 off off on)   unit  unit  minus
encode3 (tri3 zero zero zero) = maskSign3 (mask3 off off off)  unit  unit  unit
encode3 (tri3 zero zero pos)  = maskSign3 (mask3 off off on)   unit  unit  plus
encode3 (tri3 zero pos  neg)  = maskSign3 (mask3 off on  on)   unit  plus  minus
encode3 (tri3 zero pos  zero) = maskSign3 (mask3 off on  off)  unit  plus  unit
encode3 (tri3 zero pos  pos)  = maskSign3 (mask3 off on  on)   unit  plus  plus
encode3 (tri3 pos  neg  neg)  = maskSign3 (mask3 on  on  on)   plus  minus minus
encode3 (tri3 pos  neg  zero) = maskSign3 (mask3 on  on  off)  plus  minus unit
encode3 (tri3 pos  neg  pos)  = maskSign3 (mask3 on  on  on)   plus  minus plus
encode3 (tri3 pos  zero neg)  = maskSign3 (mask3 on  off on)   plus  unit  minus
encode3 (tri3 pos  zero zero) = maskSign3 (mask3 on  off off)  plus  unit  unit
encode3 (tri3 pos  zero pos)  = maskSign3 (mask3 on  off on)   plus  unit  plus
encode3 (tri3 pos  pos  neg)  = maskSign3 (mask3 on  on  on)   plus  plus  minus
encode3 (tri3 pos  pos  zero) = maskSign3 (mask3 on  on  off)  plus  plus  unit
encode3 (tri3 pos  pos  pos)  = maskSign3 (mask3 on  on  on)   plus  plus  plus

decodeSlot : (b : Bit) → ActiveSign b → Trit
decodeSlot off unit  = zero
decodeSlot on  minus = neg
decodeSlot on  plus  = pos

decode3 : MaskSign3 → Trit3
decode3 c = tri3
  (decodeSlot (mx (mask c)) (sx c))
  (decodeSlot (my (mask c)) (sy c))
  (decodeSlot (mz (mask c)) (sz c))

decode-encode-3 : ∀ t → decode3 (encode3 t) ≡ t
decode-encode-3 (tri3 neg  neg  neg)  = refl
decode-encode-3 (tri3 neg  neg  zero) = refl
decode-encode-3 (tri3 neg  neg  pos)  = refl
decode-encode-3 (tri3 neg  zero neg)  = refl
decode-encode-3 (tri3 neg  zero zero) = refl
decode-encode-3 (tri3 neg  zero pos)  = refl
decode-encode-3 (tri3 neg  pos  neg)  = refl
decode-encode-3 (tri3 neg  pos  zero) = refl
decode-encode-3 (tri3 neg  pos  pos)  = refl
decode-encode-3 (tri3 zero neg  neg)  = refl
decode-encode-3 (tri3 zero neg  zero) = refl
decode-encode-3 (tri3 zero neg  pos)  = refl
decode-encode-3 (tri3 zero zero neg)  = refl
decode-encode-3 (tri3 zero zero zero) = refl
decode-encode-3 (tri3 zero zero pos)  = refl
decode-encode-3 (tri3 zero pos  neg)  = refl
decode-encode-3 (tri3 zero pos  zero) = refl
decode-encode-3 (tri3 zero pos  pos)  = refl
decode-encode-3 (tri3 pos  neg  neg)  = refl
decode-encode-3 (tri3 pos  neg  zero) = refl
decode-encode-3 (tri3 pos  neg  pos)  = refl
decode-encode-3 (tri3 pos  zero neg)  = refl
decode-encode-3 (tri3 pos  zero zero) = refl
decode-encode-3 (tri3 pos  zero pos)  = refl
decode-encode-3 (tri3 pos  pos  neg)  = refl
decode-encode-3 (tri3 pos  pos  zero) = refl
decode-encode-3 (tri3 pos  pos  pos)  = refl

------------------------------------------------------------------------
-- The eight support masks and their Hamming-weight classes.
------------------------------------------------------------------------

data Weight : Set where
  w0 w1 w2 w3 : Weight

weight : Mask3 → Weight
weight (mask3 off off off) = w0
weight (mask3 off off on)  = w1
weight (mask3 off on  off) = w1
weight (mask3 on  off off) = w1
weight (mask3 off on  on)  = w2
weight (mask3 on  off on)  = w2
weight (mask3 on  on  off) = w2
weight (mask3 on  on  on)  = w3

invertSign : Sign → Sign
invertSign minus = plus
invertSign plus  = minus

invertTrit : Trit → Trit
invertTrit neg  = pos
invertTrit zero = zero
invertTrit pos  = neg

invert3 : Trit3 → Trit3
invert3 (tri3 a b c) = tri3 (invertTrit a) (invertTrit b) (invertTrit c)

invert-involutive : ∀ t → invert3 (invert3 t) ≡ t
invert-involutive (tri3 neg  neg  neg)  = refl
invert-involutive (tri3 neg  neg  zero) = refl
invert-involutive (tri3 neg  neg  pos)  = refl
invert-involutive (tri3 neg  zero neg)  = refl
invert-involutive (tri3 neg  zero zero) = refl
invert-involutive (tri3 neg  zero pos)  = refl
invert-involutive (tri3 neg  pos  neg)  = refl
invert-involutive (tri3 neg  pos  zero) = refl
invert-involutive (tri3 neg  pos  pos)  = refl
invert-involutive (tri3 zero neg  neg)  = refl
invert-involutive (tri3 zero neg  zero) = refl
invert-involutive (tri3 zero neg  pos)  = refl
invert-involutive (tri3 zero zero neg)  = refl
invert-involutive (tri3 zero zero zero) = refl
invert-involutive (tri3 zero zero pos)  = refl
invert-involutive (tri3 zero pos  neg)  = refl
invert-involutive (tri3 zero pos  zero) = refl
invert-involutive (tri3 zero pos  pos)  = refl
invert-involutive (tri3 pos  neg  neg)  = refl
invert-involutive (tri3 pos  neg  zero) = refl
invert-involutive (tri3 pos  neg  pos)  = refl
invert-involutive (tri3 pos  zero neg)  = refl
invert-involutive (tri3 pos  zero zero) = refl
invert-involutive (tri3 pos  zero pos)  = refl
invert-involutive (tri3 pos  pos  neg)  = refl
invert-involutive (tri3 pos  pos  zero) = refl
invert-involutive (tri3 pos  pos  pos)  = refl
