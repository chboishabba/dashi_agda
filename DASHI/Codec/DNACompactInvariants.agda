module DASHI.Codec.DNACompactInvariants where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base; A; C; G; T
  ; Axis3; axis0; axis1; axis2
  ; Line3
  )

------------------------------------------------------------------------
-- Four-symbol repetition code. The compact invariant is the two-bit base tag;
-- each encoded 3-mer has minimum Hamming distance three from every other
-- encoded codeword. This is a deterministic bound, not a probabilistic CRC
-- claim for arbitrary DNA words.

codeword : Base → Line3
codeword b axis0 = b
codeword b axis1 = b
codeword b axis2 = b

data DifferentBase : Base → Base → Set where
  A≠C : DifferentBase A C
  A≠G : DifferentBase A G
  A≠T : DifferentBase A T
  C≠A : DifferentBase C A
  C≠G : DifferentBase C G
  C≠T : DifferentBase C T
  G≠A : DifferentBase G A
  G≠C : DifferentBase G C
  G≠T : DifferentBase G T
  T≠A : DifferentBase T A
  T≠C : DifferentBase T C
  T≠G : DifferentBase T G

data Hamming3 : Line3 → Line3 → Set where
  distance3 :
    ∀ {x y} →
    DifferentBase x y →
    Hamming3 (codeword x) (codeword y)

codeword-distance3 :
  ∀ {x y} → DifferentBase x y → Hamming3 (codeword x) (codeword y)
codeword-distance3 d = distance3 d

compactTag : Base → Base
compactTag b = b

compactTag-injective : ∀ {x y} → compactTag x ≡ compactTag y → x ≡ y
compactTag-injective refl = refl

record CompactDistanceReceipt : Set where
  field
    Symbol : Set
    tag : Symbol → Base
    encoded : Symbol → Line3
    collisionFree : ∀ {x y} → tag x ≡ tag y → x ≡ y
    minimumDistanceThree :
      ∀ {x y} → DifferentBase x y → Hamming3 (encoded x) (encoded y)

compactDistanceReceipt : CompactDistanceReceipt
compactDistanceReceipt = record
  { Symbol = Base
  ; tag = compactTag
  ; encoded = codeword
  ; collisionFree = compactTag-injective
  ; minimumDistanceThree = codeword-distance3
  }

------------------------------------------------------------------------
-- Explicit probabilistic-bound surface for compact word checks. Consumers
-- must supply the randomness/ideal-hash assumptions; the denominator is not
-- silently promoted into an unconditional theorem.

record CollisionBoundAssumption : Set₁ where
  field
    Message : Set
    Digest : Set
    digest : Message → Digest
    denominator : Set
    idealUniformSyndrome : Set
    claimedBound : Set
