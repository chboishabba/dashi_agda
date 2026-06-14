module DASHI.Foundations.Base369FiniteRingLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using () renaming (_*_ to _*Nat_)

data ⊥ : Set where

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high
  ; HexTruth ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; NonaryTruth ; non-0 ; non-1 ; non-2 ; non-3 ; non-4
  ; non-5 ; non-6 ; non-7 ; non-8
  ; triXor ; triXor-identityˡ ; triXor-assoc
  ; hexXor ; hex-index ; fromHexIndex
  ; nonaryXor ; nonary-index ; fromNonaryIndex
  )

open import DASHI.Foundations.PhysicsLinearAnalysisParity using
  ( ScalarAuthoritySocket ; canonicalRealScalarAuthoritySocket )

------------------------------------------------------------------------
-- Shared witness shapes.

record ZeroDivisorWitness
  (Carrier : Set)
  (zero : Carrier)
  (_*_ : Carrier → Carrier → Carrier) :
  Set where
  field
    left :
      Carrier

    right :
      Carrier

    productIsZero :
      left * right ≡ zero

    leftNonZero :
      left ≡ zero → ⊥

    rightNonZero :
      right ≡ zero → ⊥

open ZeroDivisorWitness public

record RingAuthoritySlot : Set₁ where
  field
    Carrier :
      Set

    zero one :
      Carrier

    _+_ _*_ :
      Carrier → Carrier → Carrier

    additiveZeroL :
      (x : Carrier) → zero + x ≡ x

open RingAuthoritySlot public

------------------------------------------------------------------------
-- TriTruth: F3 with addition from Base369.triXor and concrete
-- multiplication modulo three.

triTruthMul : TriTruth → TriTruth → TriTruth
triTruthMul tri-low  _        = tri-low
triTruthMul tri-mid  x        = x
triTruthMul tri-high tri-low  = tri-low
triTruthMul tri-high tri-mid  = tri-high
triTruthMul tri-high tri-high = tri-mid

triTruthNeg : TriTruth → TriTruth
triTruthNeg tri-low  = tri-low
triTruthNeg tri-mid  = tri-high
triTruthNeg tri-high = tri-mid

triTruthAddComm :
  (x y : TriTruth) →
  triXor x y ≡ triXor y x
triTruthAddComm tri-low  tri-low  = refl
triTruthAddComm tri-low  tri-mid  = refl
triTruthAddComm tri-low  tri-high = refl
triTruthAddComm tri-mid  tri-low  = refl
triTruthAddComm tri-mid  tri-mid  = refl
triTruthAddComm tri-mid  tri-high = refl
triTruthAddComm tri-high tri-low  = refl
triTruthAddComm tri-high tri-mid  = refl
triTruthAddComm tri-high tri-high = refl

triTruthAddInvL :
  (x : TriTruth) →
  triXor (triTruthNeg x) x ≡ tri-low
triTruthAddInvL tri-low  = refl
triTruthAddInvL tri-mid  = refl
triTruthAddInvL tri-high = refl

triTruthMulComm :
  (x y : TriTruth) →
  triTruthMul x y ≡ triTruthMul y x
triTruthMulComm tri-low  tri-low  = refl
triTruthMulComm tri-low  tri-mid  = refl
triTruthMulComm tri-low  tri-high = refl
triTruthMulComm tri-mid  tri-low  = refl
triTruthMulComm tri-mid  tri-mid  = refl
triTruthMulComm tri-mid  tri-high = refl
triTruthMulComm tri-high tri-low  = refl
triTruthMulComm tri-high tri-mid  = refl
triTruthMulComm tri-high tri-high = refl

triTruthMulAssoc :
  (x y z : TriTruth) →
  triTruthMul x (triTruthMul y z) ≡
  triTruthMul (triTruthMul x y) z
triTruthMulAssoc tri-low  _        _        = refl
triTruthMulAssoc tri-mid  _        _        = refl
triTruthMulAssoc tri-high tri-low  _        = refl
triTruthMulAssoc tri-high tri-mid  _        = refl
triTruthMulAssoc tri-high tri-high tri-low  = refl
triTruthMulAssoc tri-high tri-high tri-mid  = refl
triTruthMulAssoc tri-high tri-high tri-high = refl

triTruthMulOneL :
  (x : TriTruth) →
  triTruthMul tri-mid x ≡ x
triTruthMulOneL x = refl

triTruthDistL :
  (x y z : TriTruth) →
  triTruthMul x (triXor y z) ≡
  triXor (triTruthMul x y) (triTruthMul x z)
triTruthDistL tri-low  _        _        = refl
triTruthDistL tri-mid  _        _        = refl
triTruthDistL tri-high tri-low  tri-low  = refl
triTruthDistL tri-high tri-low  tri-mid  = refl
triTruthDistL tri-high tri-low  tri-high = refl
triTruthDistL tri-high tri-mid  tri-low  = refl
triTruthDistL tri-high tri-mid  tri-mid  = refl
triTruthDistL tri-high tri-mid  tri-high = refl
triTruthDistL tri-high tri-high tri-low  = refl
triTruthDistL tri-high tri-high tri-mid  = refl
triTruthDistL tri-high tri-high tri-high = refl

record TriTruthRingLaws : Set where
  field
    addZeroL :
      (x : TriTruth) → triXor tri-low x ≡ x

    addComm :
      (x y : TriTruth) → triXor x y ≡ triXor y x

    addAssoc :
      (x y z : TriTruth) →
      triXor x (triXor y z) ≡ triXor (triXor x y) z

    addInvL :
      (x : TriTruth) → triXor (triTruthNeg x) x ≡ tri-low

    mulOneL :
      (x : TriTruth) → triTruthMul tri-mid x ≡ x

    mulComm :
      (x y : TriTruth) → triTruthMul x y ≡ triTruthMul y x

    mulAssoc :
      (x y z : TriTruth) →
      triTruthMul x (triTruthMul y z) ≡
      triTruthMul (triTruthMul x y) z

    distL :
      (x y z : TriTruth) →
      triTruthMul x (triXor y z) ≡
      triXor (triTruthMul x y) (triTruthMul x z)

open TriTruthRingLaws public

triTruthRingLaws : TriTruthRingLaws
triTruthRingLaws =
  record
    { addZeroL = triXor-identityˡ
    ; addComm = triTruthAddComm
    ; addAssoc = triXor-assoc
    ; addInvL = triTruthAddInvL
    ; mulOneL = triTruthMulOneL
    ; mulComm = triTruthMulComm
    ; mulAssoc = triTruthMulAssoc
    ; distL = triTruthDistL
    }

data TriTruthNonZero : TriTruth → Set where
  tri-mid-nonzero :
    TriTruthNonZero tri-mid

  tri-high-nonzero :
    TriTruthNonZero tri-high

triTruthInv :
  (x : TriTruth) →
  TriTruthNonZero x →
  TriTruth
triTruthInv tri-mid  tri-mid-nonzero  = tri-mid
triTruthInv tri-high tri-high-nonzero = tri-high

triTruthInvL :
  (x : TriTruth) →
  (nz : TriTruthNonZero x) →
  triTruthMul (triTruthInv x nz) x ≡ tri-mid
triTruthInvL tri-mid  tri-mid-nonzero  = refl
triTruthInvL tri-high tri-high-nonzero = refl

record TriTruthIsField : Set₁ where
  field
    ring :
      TriTruthRingLaws

    nonzero :
      TriTruth → Set

    inv :
      (x : TriTruth) → nonzero x → TriTruth

    invL :
      (x : TriTruth) →
      (nz : nonzero x) →
      triTruthMul (inv x nz) x ≡ tri-mid

open TriTruthIsField public

triTruthIsField : TriTruthIsField
triTruthIsField =
  record
    { ring = triTruthRingLaws
    ; nonzero = TriTruthNonZero
    ; inv = triTruthInv
    ; invL = triTruthInvL
    }

triTruthFieldReceipt : TriTruthIsField
triTruthFieldReceipt = triTruthIsField

------------------------------------------------------------------------
-- HexTruth: Z/6Z with concrete additive carrier and zero-divisor witness.

hexTruthMul : HexTruth → HexTruth → HexTruth
hexTruthMul x y = fromHexIndex (hex-index x *Nat hex-index y)

hexTruthRingAuthoritySlot : RingAuthoritySlot
hexTruthRingAuthoritySlot =
  record
    { Carrier = HexTruth
    ; zero = hex-0
    ; one = hex-1
    ; _+_ = hexXor
    ; _*_ = hexTruthMul
    ; additiveZeroL = λ
        { hex-0 → refl
        ; hex-1 → refl
        ; hex-2 → refl
        ; hex-3 → refl
        ; hex-4 → refl
        ; hex-5 → refl
        }
    }

data HexTruthNonZero : HexTruth → Set where
  hex-1-nonzero : HexTruthNonZero hex-1
  hex-2-nonzero : HexTruthNonZero hex-2
  hex-3-nonzero : HexTruthNonZero hex-3
  hex-4-nonzero : HexTruthNonZero hex-4
  hex-5-nonzero : HexTruthNonZero hex-5

hex-2-not-zero :
  hex-2 ≡ hex-0 → ⊥
hex-2-not-zero ()

hex-3-not-zero :
  hex-3 ≡ hex-0 → ⊥
hex-3-not-zero ()

hexZeroDivisorWitness :
  ZeroDivisorWitness HexTruth hex-0 hexTruthMul
hexZeroDivisorWitness =
  record
    { left = hex-2
    ; right = hex-3
    ; productIsZero = refl
    ; leftNonZero = hex-2-not-zero
    ; rightNonZero = hex-3-not-zero
    }

------------------------------------------------------------------------
-- NonaryTruth: Z/9Z with concrete additive carrier and zero divisors.

nonaryTruthMul : NonaryTruth → NonaryTruth → NonaryTruth
nonaryTruthMul x y = fromNonaryIndex (nonary-index x *Nat nonary-index y)

nonaryTruthRingAuthoritySlot : RingAuthoritySlot
nonaryTruthRingAuthoritySlot =
  record
    { Carrier = NonaryTruth
    ; zero = non-0
    ; one = non-1
    ; _+_ = nonaryXor
    ; _*_ = nonaryTruthMul
    ; additiveZeroL = λ
        { non-0 → refl
        ; non-1 → refl
        ; non-2 → refl
        ; non-3 → refl
        ; non-4 → refl
        ; non-5 → refl
        ; non-6 → refl
        ; non-7 → refl
        ; non-8 → refl
        }
    }

non-3-not-zero :
  non-3 ≡ non-0 → ⊥
non-3-not-zero ()

non-6-not-zero :
  non-6 ≡ non-0 → ⊥
non-6-not-zero ()

nonaryZeroDivisorWitness-3-3 :
  ZeroDivisorWitness NonaryTruth non-0 nonaryTruthMul
nonaryZeroDivisorWitness-3-3 =
  record
    { left = non-3
    ; right = non-3
    ; productIsZero = refl
    ; leftNonZero = non-3-not-zero
    ; rightNonZero = non-3-not-zero
    }

nonaryZeroDivisorWitness-3-6 :
  ZeroDivisorWitness NonaryTruth non-0 nonaryTruthMul
nonaryZeroDivisorWitness-3-6 =
  record
    { left = non-3
    ; right = non-6
    ; productIsZero = refl
    ; leftNonZero = non-3-not-zero
    ; rightNonZero = non-6-not-zero
    }

nonaryZeroDivisorWitness-6-6 :
  ZeroDivisorWitness NonaryTruth non-0 nonaryTruthMul
nonaryZeroDivisorWitness-6-6 =
  record
    { left = non-6
    ; right = non-6
    ; productIsZero = refl
    ; leftNonZero = non-6-not-zero
    ; rightNonZero = non-6-not-zero
    }

------------------------------------------------------------------------
-- Compatible scalar-field socket from the linear-analysis parity layer.

scalarFieldSocketInhabitant :
  ScalarAuthoritySocket
scalarFieldSocketInhabitant =
  canonicalRealScalarAuthoritySocket
