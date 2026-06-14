module DASHI.Foundations.Base369NonaryTruthRing where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data NonaryTruth : Set where
  non-0 non-1 non-2 non-3 non-4 non-5 non-6 non-7 non-8 :
    NonaryTruth

------------------------------------------------------------------------
-- Boolean table helpers

infixr 6 _&&_

_&&_ : Bool → Bool → Bool
true  && b = b
false && _ = false

nonaryEq : NonaryTruth → NonaryTruth → Bool
nonaryEq non-0 non-0 = true
nonaryEq non-0 _     = false
nonaryEq non-1 non-1 = true
nonaryEq non-1 _     = false
nonaryEq non-2 non-2 = true
nonaryEq non-2 _     = false
nonaryEq non-3 non-3 = true
nonaryEq non-3 _     = false
nonaryEq non-4 non-4 = true
nonaryEq non-4 _     = false
nonaryEq non-5 non-5 = true
nonaryEq non-5 _     = false
nonaryEq non-6 non-6 = true
nonaryEq non-6 _     = false
nonaryEq non-7 non-7 = true
nonaryEq non-7 _     = false
nonaryEq non-8 non-8 = true
nonaryEq non-8 _     = false

allNonary : (NonaryTruth → Bool) → Bool
allNonary p =
  p non-0 && p non-1 && p non-2 && p non-3 && p non-4 &&
  p non-5 && p non-6 && p non-7 && p non-8

allNonary2 : (NonaryTruth → NonaryTruth → Bool) → Bool
allNonary2 p = allNonary λ a → allNonary λ b → p a b

allNonary3 :
  (NonaryTruth → NonaryTruth → NonaryTruth → Bool) →
  Bool
allNonary3 p = allNonary λ a → allNonary λ b → allNonary λ c → p a b c

------------------------------------------------------------------------
-- Self-contained Z/9Z ring operations on NonaryTruth.

nonaryZero : NonaryTruth
nonaryZero = non-0

nonaryOne : NonaryTruth
nonaryOne = non-1

nonaryAdd : NonaryTruth → NonaryTruth → NonaryTruth
nonaryAdd non-0 b     = b
nonaryAdd non-1 non-0 = non-1
nonaryAdd non-1 non-1 = non-2
nonaryAdd non-1 non-2 = non-3
nonaryAdd non-1 non-3 = non-4
nonaryAdd non-1 non-4 = non-5
nonaryAdd non-1 non-5 = non-6
nonaryAdd non-1 non-6 = non-7
nonaryAdd non-1 non-7 = non-8
nonaryAdd non-1 non-8 = non-0
nonaryAdd non-2 non-0 = non-2
nonaryAdd non-2 non-1 = non-3
nonaryAdd non-2 non-2 = non-4
nonaryAdd non-2 non-3 = non-5
nonaryAdd non-2 non-4 = non-6
nonaryAdd non-2 non-5 = non-7
nonaryAdd non-2 non-6 = non-8
nonaryAdd non-2 non-7 = non-0
nonaryAdd non-2 non-8 = non-1
nonaryAdd non-3 non-0 = non-3
nonaryAdd non-3 non-1 = non-4
nonaryAdd non-3 non-2 = non-5
nonaryAdd non-3 non-3 = non-6
nonaryAdd non-3 non-4 = non-7
nonaryAdd non-3 non-5 = non-8
nonaryAdd non-3 non-6 = non-0
nonaryAdd non-3 non-7 = non-1
nonaryAdd non-3 non-8 = non-2
nonaryAdd non-4 non-0 = non-4
nonaryAdd non-4 non-1 = non-5
nonaryAdd non-4 non-2 = non-6
nonaryAdd non-4 non-3 = non-7
nonaryAdd non-4 non-4 = non-8
nonaryAdd non-4 non-5 = non-0
nonaryAdd non-4 non-6 = non-1
nonaryAdd non-4 non-7 = non-2
nonaryAdd non-4 non-8 = non-3
nonaryAdd non-5 non-0 = non-5
nonaryAdd non-5 non-1 = non-6
nonaryAdd non-5 non-2 = non-7
nonaryAdd non-5 non-3 = non-8
nonaryAdd non-5 non-4 = non-0
nonaryAdd non-5 non-5 = non-1
nonaryAdd non-5 non-6 = non-2
nonaryAdd non-5 non-7 = non-3
nonaryAdd non-5 non-8 = non-4
nonaryAdd non-6 non-0 = non-6
nonaryAdd non-6 non-1 = non-7
nonaryAdd non-6 non-2 = non-8
nonaryAdd non-6 non-3 = non-0
nonaryAdd non-6 non-4 = non-1
nonaryAdd non-6 non-5 = non-2
nonaryAdd non-6 non-6 = non-3
nonaryAdd non-6 non-7 = non-4
nonaryAdd non-6 non-8 = non-5
nonaryAdd non-7 non-0 = non-7
nonaryAdd non-7 non-1 = non-8
nonaryAdd non-7 non-2 = non-0
nonaryAdd non-7 non-3 = non-1
nonaryAdd non-7 non-4 = non-2
nonaryAdd non-7 non-5 = non-3
nonaryAdd non-7 non-6 = non-4
nonaryAdd non-7 non-7 = non-5
nonaryAdd non-7 non-8 = non-6
nonaryAdd non-8 non-0 = non-8
nonaryAdd non-8 non-1 = non-0
nonaryAdd non-8 non-2 = non-1
nonaryAdd non-8 non-3 = non-2
nonaryAdd non-8 non-4 = non-3
nonaryAdd non-8 non-5 = non-4
nonaryAdd non-8 non-6 = non-5
nonaryAdd non-8 non-7 = non-6
nonaryAdd non-8 non-8 = non-7

nonaryXor : NonaryTruth → NonaryTruth → NonaryTruth
nonaryXor = nonaryAdd

nonaryNeg : NonaryTruth → NonaryTruth
nonaryNeg non-0 = non-0
nonaryNeg non-1 = non-8
nonaryNeg non-2 = non-7
nonaryNeg non-3 = non-6
nonaryNeg non-4 = non-5
nonaryNeg non-5 = non-4
nonaryNeg non-6 = non-3
nonaryNeg non-7 = non-2
nonaryNeg non-8 = non-1

nonarySub : NonaryTruth → NonaryTruth → NonaryTruth
nonarySub a b = nonaryAdd a (nonaryNeg b)

nonaryMul : NonaryTruth → NonaryTruth → NonaryTruth
nonaryMul non-0 _     = non-0
nonaryMul non-1 b     = b
nonaryMul non-2 non-0 = non-0
nonaryMul non-2 non-1 = non-2
nonaryMul non-2 non-2 = non-4
nonaryMul non-2 non-3 = non-6
nonaryMul non-2 non-4 = non-8
nonaryMul non-2 non-5 = non-1
nonaryMul non-2 non-6 = non-3
nonaryMul non-2 non-7 = non-5
nonaryMul non-2 non-8 = non-7
nonaryMul non-3 non-0 = non-0
nonaryMul non-3 non-1 = non-3
nonaryMul non-3 non-2 = non-6
nonaryMul non-3 non-3 = non-0
nonaryMul non-3 non-4 = non-3
nonaryMul non-3 non-5 = non-6
nonaryMul non-3 non-6 = non-0
nonaryMul non-3 non-7 = non-3
nonaryMul non-3 non-8 = non-6
nonaryMul non-4 non-0 = non-0
nonaryMul non-4 non-1 = non-4
nonaryMul non-4 non-2 = non-8
nonaryMul non-4 non-3 = non-3
nonaryMul non-4 non-4 = non-7
nonaryMul non-4 non-5 = non-2
nonaryMul non-4 non-6 = non-6
nonaryMul non-4 non-7 = non-1
nonaryMul non-4 non-8 = non-5
nonaryMul non-5 non-0 = non-0
nonaryMul non-5 non-1 = non-5
nonaryMul non-5 non-2 = non-1
nonaryMul non-5 non-3 = non-6
nonaryMul non-5 non-4 = non-2
nonaryMul non-5 non-5 = non-7
nonaryMul non-5 non-6 = non-3
nonaryMul non-5 non-7 = non-8
nonaryMul non-5 non-8 = non-4
nonaryMul non-6 non-0 = non-0
nonaryMul non-6 non-1 = non-6
nonaryMul non-6 non-2 = non-3
nonaryMul non-6 non-3 = non-0
nonaryMul non-6 non-4 = non-6
nonaryMul non-6 non-5 = non-3
nonaryMul non-6 non-6 = non-0
nonaryMul non-6 non-7 = non-6
nonaryMul non-6 non-8 = non-3
nonaryMul non-7 non-0 = non-0
nonaryMul non-7 non-1 = non-7
nonaryMul non-7 non-2 = non-5
nonaryMul non-7 non-3 = non-3
nonaryMul non-7 non-4 = non-1
nonaryMul non-7 non-5 = non-8
nonaryMul non-7 non-6 = non-6
nonaryMul non-7 non-7 = non-4
nonaryMul non-7 non-8 = non-2
nonaryMul non-8 non-0 = non-0
nonaryMul non-8 non-1 = non-8
nonaryMul non-8 non-2 = non-7
nonaryMul non-8 non-3 = non-6
nonaryMul non-8 non-4 = non-5
nonaryMul non-8 non-5 = non-4
nonaryMul non-8 non-6 = non-3
nonaryMul non-8 non-7 = non-2
nonaryMul non-8 non-8 = non-1

------------------------------------------------------------------------
-- Pointwise proof surfaces for the small laws.

nonaryNeg-involutive : (a : NonaryTruth) → nonaryNeg (nonaryNeg a) ≡ a
nonaryNeg-involutive non-0 = refl
nonaryNeg-involutive non-1 = refl
nonaryNeg-involutive non-2 = refl
nonaryNeg-involutive non-3 = refl
nonaryNeg-involutive non-4 = refl
nonaryNeg-involutive non-5 = refl
nonaryNeg-involutive non-6 = refl
nonaryNeg-involutive non-7 = refl
nonaryNeg-involutive non-8 = refl

nonaryAdd-inverseˡ : (a : NonaryTruth) → nonaryAdd (nonaryNeg a) a ≡ nonaryZero
nonaryAdd-inverseˡ non-0 = refl
nonaryAdd-inverseˡ non-1 = refl
nonaryAdd-inverseˡ non-2 = refl
nonaryAdd-inverseˡ non-3 = refl
nonaryAdd-inverseˡ non-4 = refl
nonaryAdd-inverseˡ non-5 = refl
nonaryAdd-inverseˡ non-6 = refl
nonaryAdd-inverseˡ non-7 = refl
nonaryAdd-inverseˡ non-8 = refl

nonaryMul-identityˡ : (a : NonaryTruth) → nonaryMul nonaryOne a ≡ a
nonaryMul-identityˡ a = refl

nonaryMul-identityʳ : (a : NonaryTruth) → nonaryMul a nonaryOne ≡ a
nonaryMul-identityʳ non-0 = refl
nonaryMul-identityʳ non-1 = refl
nonaryMul-identityʳ non-2 = refl
nonaryMul-identityʳ non-3 = refl
nonaryMul-identityʳ non-4 = refl
nonaryMul-identityʳ non-5 = refl
nonaryMul-identityʳ non-6 = refl
nonaryMul-identityʳ non-7 = refl
nonaryMul-identityʳ non-8 = refl

nonaryMul-zeroˡ : (a : NonaryTruth) → nonaryMul nonaryZero a ≡ nonaryZero
nonaryMul-zeroˡ a = refl

nonaryMul-zeroʳ : (a : NonaryTruth) → nonaryMul a nonaryZero ≡ nonaryZero
nonaryMul-zeroʳ non-0 = refl
nonaryMul-zeroʳ non-1 = refl
nonaryMul-zeroʳ non-2 = refl
nonaryMul-zeroʳ non-3 = refl
nonaryMul-zeroʳ non-4 = refl
nonaryMul-zeroʳ non-5 = refl
nonaryMul-zeroʳ non-6 = refl
nonaryMul-zeroʳ non-7 = refl
nonaryMul-zeroʳ non-8 = refl

------------------------------------------------------------------------
-- Exhaustive table receipts for heavier ring laws.

nonaryAdd-comm-table : Bool
nonaryAdd-comm-table =
  allNonary2 λ a b → nonaryEq (nonaryAdd a b) (nonaryAdd b a)

nonaryAdd-comm-receipt : nonaryAdd-comm-table ≡ true
nonaryAdd-comm-receipt = refl

nonaryAdd-assoc-table : Bool
nonaryAdd-assoc-table =
  allNonary3 λ a b c →
    nonaryEq (nonaryAdd a (nonaryAdd b c))
             (nonaryAdd (nonaryAdd a b) c)

nonaryAdd-assoc-receipt : nonaryAdd-assoc-table ≡ true
nonaryAdd-assoc-receipt = refl

nonaryAdd-identity-table : Bool
nonaryAdd-identity-table =
  allNonary λ a →
    nonaryEq (nonaryAdd nonaryZero a) a &&
    nonaryEq (nonaryAdd a nonaryZero) a

nonaryAdd-identity-receipt : nonaryAdd-identity-table ≡ true
nonaryAdd-identity-receipt = refl

nonaryAdd-inverse-table : Bool
nonaryAdd-inverse-table =
  allNonary λ a →
    nonaryEq (nonaryAdd (nonaryNeg a) a) nonaryZero &&
    nonaryEq (nonaryAdd a (nonaryNeg a)) nonaryZero

nonaryAdd-inverse-receipt : nonaryAdd-inverse-table ≡ true
nonaryAdd-inverse-receipt = refl

nonaryMul-comm-table : Bool
nonaryMul-comm-table =
  allNonary2 λ a b → nonaryEq (nonaryMul a b) (nonaryMul b a)

nonaryMul-comm-receipt : nonaryMul-comm-table ≡ true
nonaryMul-comm-receipt = refl

nonaryMul-assoc-table : Bool
nonaryMul-assoc-table =
  allNonary3 λ a b c →
    nonaryEq (nonaryMul a (nonaryMul b c))
             (nonaryMul (nonaryMul a b) c)

nonaryMul-assoc-receipt : nonaryMul-assoc-table ≡ true
nonaryMul-assoc-receipt = refl

nonaryMul-identity-table : Bool
nonaryMul-identity-table =
  allNonary λ a →
    nonaryEq (nonaryMul nonaryOne a) a &&
    nonaryEq (nonaryMul a nonaryOne) a

nonaryMul-identity-receipt : nonaryMul-identity-table ≡ true
nonaryMul-identity-receipt = refl

nonaryMul-zero-table : Bool
nonaryMul-zero-table =
  allNonary λ a →
    nonaryEq (nonaryMul nonaryZero a) nonaryZero &&
    nonaryEq (nonaryMul a nonaryZero) nonaryZero

nonaryMul-zero-receipt : nonaryMul-zero-table ≡ true
nonaryMul-zero-receipt = refl

nonaryMul-distribˡ-table : Bool
nonaryMul-distribˡ-table =
  allNonary3 λ a b c →
    nonaryEq (nonaryMul a (nonaryAdd b c))
             (nonaryAdd (nonaryMul a b) (nonaryMul a c))

nonaryMul-distribˡ-receipt : nonaryMul-distribˡ-table ≡ true
nonaryMul-distribˡ-receipt = refl

nonaryMul-distribʳ-table : Bool
nonaryMul-distribʳ-table =
  allNonary3 λ a b c →
    nonaryEq (nonaryMul (nonaryAdd a b) c)
             (nonaryAdd (nonaryMul a c) (nonaryMul b c))

nonaryMul-distribʳ-receipt : nonaryMul-distribʳ-table ≡ true
nonaryMul-distribʳ-receipt = refl

nonaryRingLaws-table : Bool
nonaryRingLaws-table =
  nonaryAdd-comm-table &&
  nonaryAdd-assoc-table &&
  nonaryAdd-identity-table &&
  nonaryAdd-inverse-table &&
  nonaryMul-comm-table &&
  nonaryMul-assoc-table &&
  nonaryMul-identity-table &&
  nonaryMul-zero-table &&
  nonaryMul-distribˡ-table &&
  nonaryMul-distribʳ-table

nonaryRingLaws-receipt : nonaryRingLaws-table ≡ true
nonaryRingLaws-receipt = refl

record NonaryRingReceipt : Set where
  field
    addCommTable :
      Bool

    addCommVerified :
      addCommTable ≡ true

    addAssocTable :
      Bool

    addAssocVerified :
      addAssocTable ≡ true

    addIdentityTable :
      Bool

    addIdentityVerified :
      addIdentityTable ≡ true

    addInverseTable :
      Bool

    addInverseVerified :
      addInverseTable ≡ true

    mulCommTable :
      Bool

    mulCommVerified :
      mulCommTable ≡ true

    mulAssocTable :
      Bool

    mulAssocVerified :
      mulAssocTable ≡ true

    mulIdentityTable :
      Bool

    mulIdentityVerified :
      mulIdentityTable ≡ true

    mulZeroTable :
      Bool

    mulZeroVerified :
      mulZeroTable ≡ true

    mulDistribLeftTable :
      Bool

    mulDistribLeftVerified :
      mulDistribLeftTable ≡ true

    mulDistribRightTable :
      Bool

    mulDistribRightVerified :
      mulDistribRightTable ≡ true

open NonaryRingReceipt public

canonicalNonaryRingReceipt : NonaryRingReceipt
canonicalNonaryRingReceipt =
  record
    { addCommTable =
        nonaryAdd-comm-table
    ; addCommVerified =
        nonaryAdd-comm-receipt
    ; addAssocTable =
        nonaryAdd-assoc-table
    ; addAssocVerified =
        nonaryAdd-assoc-receipt
    ; addIdentityTable =
        nonaryAdd-identity-table
    ; addIdentityVerified =
        nonaryAdd-identity-receipt
    ; addInverseTable =
        nonaryAdd-inverse-table
    ; addInverseVerified =
        nonaryAdd-inverse-receipt
    ; mulCommTable =
        nonaryMul-comm-table
    ; mulCommVerified =
        nonaryMul-comm-receipt
    ; mulAssocTable =
        nonaryMul-assoc-table
    ; mulAssocVerified =
        nonaryMul-assoc-receipt
    ; mulIdentityTable =
        nonaryMul-identity-table
    ; mulIdentityVerified =
        nonaryMul-identity-receipt
    ; mulZeroTable =
        nonaryMul-zero-table
    ; mulZeroVerified =
        nonaryMul-zero-receipt
    ; mulDistribLeftTable =
        nonaryMul-distribˡ-table
    ; mulDistribLeftVerified =
        nonaryMul-distribˡ-receipt
    ; mulDistribRightTable =
        nonaryMul-distribʳ-table
    ; mulDistribRightVerified =
        nonaryMul-distribʳ-receipt
    }

------------------------------------------------------------------------
-- Z/9Z is a ring with zero divisors, not a field.

non-3*non-3=non-0 : nonaryMul non-3 non-3 ≡ non-0
non-3*non-3=non-0 = refl

non-3*non-6=non-0 : nonaryMul non-3 non-6 ≡ non-0
non-3*non-6=non-0 = refl

non-6*non-6=non-0 : nonaryMul non-6 non-6 ≡ non-0
non-6*non-6=non-0 = refl

nonaryIsField : Bool
nonaryIsField = false

nonaryIsField-receipt : nonaryIsField ≡ false
nonaryIsField-receipt = refl

nonaryNotField : Bool
nonaryNotField = true

nonaryNotField-receipt : nonaryNotField ≡ true
nonaryNotField-receipt = refl

record NonaryNotFieldReceipt : Set where
  field
    hasZeroDivisors :
      Bool

    hasZeroDivisorsVerified :
      hasZeroDivisors ≡ true

    fieldClaim :
      Bool

    fieldClaimRejected :
      fieldClaim ≡ false

open NonaryNotFieldReceipt public

canonicalNonaryNotFieldReceipt : NonaryNotFieldReceipt
canonicalNonaryNotFieldReceipt =
  record
    { hasZeroDivisors =
        true
    ; hasZeroDivisorsVerified =
        refl
    ; fieldClaim =
        nonaryIsField
    ; fieldClaimRejected =
        nonaryIsField-receipt
    }
