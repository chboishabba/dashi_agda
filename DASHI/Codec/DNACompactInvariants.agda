module DASHI.Codec.DNACompactInvariants where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Codec.DNAFirstFormalism using
  ( Base; A; C; G; T
  ; Axis3; axis0; axis1; axis2
  ; Line3
  )

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
    tag : Base → Base
    encoded : Base → Line3
    collisionFree : ∀ {x y} → tag x ≡ tag y → x ≡ y
    minimumDistanceThree :
      ∀ {x y} → DifferentBase x y → Hamming3 (encoded x) (encoded y)

compactDistanceReceipt : CompactDistanceReceipt
compactDistanceReceipt = record
  { tag = compactTag
  ; encoded = codeword
  ; collisionFree = compactTag-injective
  ; minimumDistanceThree = codeword-distance3
  }

record CollisionBoundAssumption : Set₁ where
  field
    Message : Set
    Digest : Set
    digest : Message → Digest
    denominator : Set
    idealUniformSyndrome : Set
    claimedBound : Set
