module DASHI.Codec.TriadicMaskSignFactorization where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- Exact support/sign factorisation for the canonical DASHI trit.
--
-- This is a lossless algebraic statement.  It does not assume a source
-- distribution, entropy model, or rANS implementation.

data Sign : Set where
  negative : Sign
  positive : Sign

data FactorizedTrit : Set where
  inactive : FactorizedTrit
  active   : Sign → FactorizedTrit

encodeTrit : Trit → FactorizedTrit
encodeTrit neg = active negative
encodeTrit zer = inactive
encodeTrit pos = active positive

decodeTrit : FactorizedTrit → Trit
decodeTrit inactive          = zer
decodeTrit (active negative) = neg
decodeTrit (active positive) = pos

decode-encode : ∀ t → decodeTrit (encodeTrit t) ≡ t
decode-encode neg = refl
decode-encode zer = refl
decode-encode pos = refl

encode-decode : ∀ f → encodeTrit (decodeTrit f) ≡ f
encode-decode inactive          = refl
encode-decode (active negative) = refl
encode-decode (active positive) = refl

------------------------------------------------------------------------
-- Three-trit symbols.

record Triple (A : Set) : Set where
  constructor triple
  field
    first  : A
    second : A
    third  : A
open Triple public

mapTriple : ∀ {A B} → (A → B) → Triple A → Triple B
mapTriple f (triple x y z) = triple (f x) (f y) (f z)

encodeTriple : Triple Trit → Triple FactorizedTrit
encodeTriple = mapTriple encodeTrit

decodeTriple : Triple FactorizedTrit → Triple Trit
decodeTriple = mapTriple decodeTrit

decodeTriple-encodeTriple :
  ∀ u → decodeTriple (encodeTriple u) ≡ u
decodeTriple-encodeTriple (triple neg neg neg) = refl
decodeTriple-encodeTriple (triple neg neg zer) = refl
decodeTriple-encodeTriple (triple neg neg pos) = refl
decodeTriple-encodeTriple (triple neg zer neg) = refl
decodeTriple-encodeTriple (triple neg zer zer) = refl
decodeTriple-encodeTriple (triple neg zer pos) = refl
decodeTriple-encodeTriple (triple neg pos neg) = refl
decodeTriple-encodeTriple (triple neg pos zer) = refl
decodeTriple-encodeTriple (triple neg pos pos) = refl
decodeTriple-encodeTriple (triple zer neg neg) = refl
decodeTriple-encodeTriple (triple zer neg zer) = refl
decodeTriple-encodeTriple (triple zer neg pos) = refl
decodeTriple-encodeTriple (triple zer zer neg) = refl
decodeTriple-encodeTriple (triple zer zer zer) = refl
decodeTriple-encodeTriple (triple zer zer pos) = refl
decodeTriple-encodeTriple (triple zer pos neg) = refl
decodeTriple-encodeTriple (triple zer pos zer) = refl
decodeTriple-encodeTriple (triple zer pos pos) = refl
decodeTriple-encodeTriple (triple pos neg neg) = refl
decodeTriple-encodeTriple (triple pos neg zer) = refl
decodeTriple-encodeTriple (triple pos neg pos) = refl
decodeTriple-encodeTriple (triple pos zer neg) = refl
decodeTriple-encodeTriple (triple pos zer zer) = refl
decodeTriple-encodeTriple (triple pos zer pos) = refl
decodeTriple-encodeTriple (triple pos pos neg) = refl
decodeTriple-encodeTriple (triple pos pos zer) = refl
decodeTriple-encodeTriple (triple pos pos pos) = refl

encodeTriple-decodeTriple :
  ∀ f → encodeTriple (decodeTriple f) ≡ f
encodeTriple-decodeTriple (triple inactive inactive inactive) = refl
encodeTriple-decodeTriple (triple inactive inactive (active negative)) = refl
encodeTriple-decodeTriple (triple inactive inactive (active positive)) = refl
encodeTriple-decodeTriple (triple inactive (active negative) inactive) = refl
encodeTriple-decodeTriple (triple inactive (active negative) (active negative)) = refl
encodeTriple-decodeTriple (triple inactive (active negative) (active positive)) = refl
encodeTriple-decodeTriple (triple inactive (active positive) inactive) = refl
encodeTriple-decodeTriple (triple inactive (active positive) (active negative)) = refl
encodeTriple-decodeTriple (triple inactive (active positive) (active positive)) = refl
encodeTriple-decodeTriple (triple (active negative) inactive inactive) = refl
encodeTriple-decodeTriple (triple (active negative) inactive (active negative)) = refl
encodeTriple-decodeTriple (triple (active negative) inactive (active positive)) = refl
encodeTriple-decodeTriple (triple (active negative) (active negative) inactive) = refl
encodeTriple-decodeTriple (triple (active negative) (active negative) (active negative)) = refl
encodeTriple-decodeTriple (triple (active negative) (active negative) (active positive)) = refl
encodeTriple-decodeTriple (triple (active negative) (active positive) inactive) = refl
encodeTriple-decodeTriple (triple (active negative) (active positive) (active negative)) = refl
encodeTriple-decodeTriple (triple (active negative) (active positive) (active positive)) = refl
encodeTriple-decodeTriple (triple (active positive) inactive inactive) = refl
encodeTriple-decodeTriple (triple (active positive) inactive (active negative)) = refl
encodeTriple-decodeTriple (triple (active positive) inactive (active positive)) = refl
encodeTriple-decodeTriple (triple (active positive) (active negative) inactive) = refl
encodeTriple-decodeTriple (triple (active positive) (active negative) (active negative)) = refl
encodeTriple-decodeTriple (triple (active positive) (active negative) (active positive)) = refl
encodeTriple-decodeTriple (triple (active positive) (active positive) inactive) = refl
encodeTriple-decodeTriple (triple (active positive) (active positive) (active negative)) = refl
encodeTriple-decodeTriple (triple (active positive) (active positive) (active positive)) = refl

------------------------------------------------------------------------
-- The projected support mask has exactly eight shapes.

data Mask3 : Set where
  mask000 mask001 mask010 mask011 : Mask3
  mask100 mask101 mask110 mask111 : Mask3

isActive : FactorizedTrit → Nat
isActive inactive  = zero
isActive (active _) = suc zero

maskOf : Triple FactorizedTrit → Mask3
maskOf (triple inactive inactive inactive) = mask000
maskOf (triple inactive inactive (active _)) = mask001
maskOf (triple inactive (active _) inactive) = mask010
maskOf (triple inactive (active _) (active _)) = mask011
maskOf (triple (active _) inactive inactive) = mask100
maskOf (triple (active _) inactive (active _)) = mask101
maskOf (triple (active _) (active _) inactive) = mask110
maskOf (triple (active _) (active _) (active _)) = mask111

activeCount : Triple FactorizedTrit → Nat
activeCount (triple x y z) = isActive x + isActive y + isActive z

-- State count by active support size:
-- C(3,0)2^0 + C(3,1)2^1 + C(3,2)2^2 + C(3,3)2^3
-- = 1 + 6 + 12 + 8 = 27.
maskSignStateCount : Nat
maskSignStateCount = 1 + 6 + 12 + 8

maskSignStateCount-is-27 : maskSignStateCount ≡ 27
maskSignStateCount-is-27 = refl
