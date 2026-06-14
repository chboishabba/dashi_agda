module DASHI.Foundations.Base369TriTruthField where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( TriTruth
  ; tri-low ; tri-mid ; tri-high
  ; triXor
  )

infixr 4 _,_ _×_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

triZero : TriTruth
triZero = tri-low

triOne : TriTruth
triOne = tri-mid

triAdd : TriTruth → TriTruth → TriTruth
triAdd = triXor

triNeg : TriTruth → TriTruth
triNeg tri-low  = tri-low
triNeg tri-mid  = tri-high
triNeg tri-high = tri-mid

triMul : TriTruth → TriTruth → TriTruth
triMul tri-low  _        = tri-low
triMul tri-mid  b        = b
triMul tri-high tri-low  = tri-low
triMul tri-high tri-mid  = tri-high
triMul tri-high tri-high = tri-mid

triInv : TriTruth → TriTruth
triInv tri-low  = tri-low
triInv tri-mid  = tri-mid
triInv tri-high = tri-high

triIsZero : TriTruth → Bool
triIsZero tri-low  = true
triIsZero tri-mid  = false
triIsZero tri-high = false

_∨ᵇ_ : Bool → Bool → Bool
true  ∨ᵇ _ = true
false ∨ᵇ b = b

_⇒ᵇ_ : Bool → Bool → Bool
true  ⇒ᵇ b = b
false ⇒ᵇ _ = true

triNoZeroDivisorPairBool : TriTruth → TriTruth → Bool
triNoZeroDivisorPairBool a b =
  triIsZero (triMul a b) ⇒ᵇ (triIsZero a ∨ᵇ triIsZero b)

triAdd-comm : ∀ a b → triAdd a b ≡ triAdd b a
triAdd-comm tri-low  tri-low  = refl
triAdd-comm tri-low  tri-mid  = refl
triAdd-comm tri-low  tri-high = refl
triAdd-comm tri-mid  tri-low  = refl
triAdd-comm tri-mid  tri-mid  = refl
triAdd-comm tri-mid  tri-high = refl
triAdd-comm tri-high tri-low  = refl
triAdd-comm tri-high tri-mid  = refl
triAdd-comm tri-high tri-high = refl

triAdd-assoc : ∀ a b c → triAdd a (triAdd b c) ≡ triAdd (triAdd a b) c
triAdd-assoc tri-low  tri-low  tri-low  = refl
triAdd-assoc tri-low  tri-low  tri-mid  = refl
triAdd-assoc tri-low  tri-low  tri-high = refl
triAdd-assoc tri-low  tri-mid  tri-low  = refl
triAdd-assoc tri-low  tri-mid  tri-mid  = refl
triAdd-assoc tri-low  tri-mid  tri-high = refl
triAdd-assoc tri-low  tri-high tri-low  = refl
triAdd-assoc tri-low  tri-high tri-mid  = refl
triAdd-assoc tri-low  tri-high tri-high = refl
triAdd-assoc tri-mid  tri-low  tri-low  = refl
triAdd-assoc tri-mid  tri-low  tri-mid  = refl
triAdd-assoc tri-mid  tri-low  tri-high = refl
triAdd-assoc tri-mid  tri-mid  tri-low  = refl
triAdd-assoc tri-mid  tri-mid  tri-mid  = refl
triAdd-assoc tri-mid  tri-mid  tri-high = refl
triAdd-assoc tri-mid  tri-high tri-low  = refl
triAdd-assoc tri-mid  tri-high tri-mid  = refl
triAdd-assoc tri-mid  tri-high tri-high = refl
triAdd-assoc tri-high tri-low  tri-low  = refl
triAdd-assoc tri-high tri-low  tri-mid  = refl
triAdd-assoc tri-high tri-low  tri-high = refl
triAdd-assoc tri-high tri-mid  tri-low  = refl
triAdd-assoc tri-high tri-mid  tri-mid  = refl
triAdd-assoc tri-high tri-mid  tri-high = refl
triAdd-assoc tri-high tri-high tri-low  = refl
triAdd-assoc tri-high tri-high tri-mid  = refl
triAdd-assoc tri-high tri-high tri-high = refl

triAdd-identityˡ : ∀ a → triAdd triZero a ≡ a
triAdd-identityˡ tri-low  = refl
triAdd-identityˡ tri-mid  = refl
triAdd-identityˡ tri-high = refl

triAdd-identityʳ : ∀ a → triAdd a triZero ≡ a
triAdd-identityʳ tri-low  = refl
triAdd-identityʳ tri-mid  = refl
triAdd-identityʳ tri-high = refl

triAdd-inverseˡ : ∀ a → triAdd (triNeg a) a ≡ triZero
triAdd-inverseˡ tri-low  = refl
triAdd-inverseˡ tri-mid  = refl
triAdd-inverseˡ tri-high = refl

triAdd-inverseʳ : ∀ a → triAdd a (triNeg a) ≡ triZero
triAdd-inverseʳ tri-low  = refl
triAdd-inverseʳ tri-mid  = refl
triAdd-inverseʳ tri-high = refl

triNeg-involutive : ∀ a → triNeg (triNeg a) ≡ a
triNeg-involutive tri-low  = refl
triNeg-involutive tri-mid  = refl
triNeg-involutive tri-high = refl

triMul-comm : ∀ a b → triMul a b ≡ triMul b a
triMul-comm tri-low  tri-low  = refl
triMul-comm tri-low  tri-mid  = refl
triMul-comm tri-low  tri-high = refl
triMul-comm tri-mid  tri-low  = refl
triMul-comm tri-mid  tri-mid  = refl
triMul-comm tri-mid  tri-high = refl
triMul-comm tri-high tri-low  = refl
triMul-comm tri-high tri-mid  = refl
triMul-comm tri-high tri-high = refl

triMul-assoc : ∀ a b c → triMul a (triMul b c) ≡ triMul (triMul a b) c
triMul-assoc tri-low  tri-low  tri-low  = refl
triMul-assoc tri-low  tri-low  tri-mid  = refl
triMul-assoc tri-low  tri-low  tri-high = refl
triMul-assoc tri-low  tri-mid  tri-low  = refl
triMul-assoc tri-low  tri-mid  tri-mid  = refl
triMul-assoc tri-low  tri-mid  tri-high = refl
triMul-assoc tri-low  tri-high tri-low  = refl
triMul-assoc tri-low  tri-high tri-mid  = refl
triMul-assoc tri-low  tri-high tri-high = refl
triMul-assoc tri-mid  tri-low  tri-low  = refl
triMul-assoc tri-mid  tri-low  tri-mid  = refl
triMul-assoc tri-mid  tri-low  tri-high = refl
triMul-assoc tri-mid  tri-mid  tri-low  = refl
triMul-assoc tri-mid  tri-mid  tri-mid  = refl
triMul-assoc tri-mid  tri-mid  tri-high = refl
triMul-assoc tri-mid  tri-high tri-low  = refl
triMul-assoc tri-mid  tri-high tri-mid  = refl
triMul-assoc tri-mid  tri-high tri-high = refl
triMul-assoc tri-high tri-low  tri-low  = refl
triMul-assoc tri-high tri-low  tri-mid  = refl
triMul-assoc tri-high tri-low  tri-high = refl
triMul-assoc tri-high tri-mid  tri-low  = refl
triMul-assoc tri-high tri-mid  tri-mid  = refl
triMul-assoc tri-high tri-mid  tri-high = refl
triMul-assoc tri-high tri-high tri-low  = refl
triMul-assoc tri-high tri-high tri-mid  = refl
triMul-assoc tri-high tri-high tri-high = refl

triMul-zeroˡ : ∀ a → triMul triZero a ≡ triZero
triMul-zeroˡ tri-low  = refl
triMul-zeroˡ tri-mid  = refl
triMul-zeroˡ tri-high = refl

triMul-zeroʳ : ∀ a → triMul a triZero ≡ triZero
triMul-zeroʳ tri-low  = refl
triMul-zeroʳ tri-mid  = refl
triMul-zeroʳ tri-high = refl

triMul-identityˡ : ∀ a → triMul triOne a ≡ a
triMul-identityˡ tri-low  = refl
triMul-identityˡ tri-mid  = refl
triMul-identityˡ tri-high = refl

triMul-identityʳ : ∀ a → triMul a triOne ≡ a
triMul-identityʳ tri-low  = refl
triMul-identityʳ tri-mid  = refl
triMul-identityʳ tri-high = refl

triDistribˡ : ∀ a b c → triMul a (triAdd b c) ≡ triAdd (triMul a b) (triMul a c)
triDistribˡ tri-low  tri-low  tri-low  = refl
triDistribˡ tri-low  tri-low  tri-mid  = refl
triDistribˡ tri-low  tri-low  tri-high = refl
triDistribˡ tri-low  tri-mid  tri-low  = refl
triDistribˡ tri-low  tri-mid  tri-mid  = refl
triDistribˡ tri-low  tri-mid  tri-high = refl
triDistribˡ tri-low  tri-high tri-low  = refl
triDistribˡ tri-low  tri-high tri-mid  = refl
triDistribˡ tri-low  tri-high tri-high = refl
triDistribˡ tri-mid  tri-low  tri-low  = refl
triDistribˡ tri-mid  tri-low  tri-mid  = refl
triDistribˡ tri-mid  tri-low  tri-high = refl
triDistribˡ tri-mid  tri-mid  tri-low  = refl
triDistribˡ tri-mid  tri-mid  tri-mid  = refl
triDistribˡ tri-mid  tri-mid  tri-high = refl
triDistribˡ tri-mid  tri-high tri-low  = refl
triDistribˡ tri-mid  tri-high tri-mid  = refl
triDistribˡ tri-mid  tri-high tri-high = refl
triDistribˡ tri-high tri-low  tri-low  = refl
triDistribˡ tri-high tri-low  tri-mid  = refl
triDistribˡ tri-high tri-low  tri-high = refl
triDistribˡ tri-high tri-mid  tri-low  = refl
triDistribˡ tri-high tri-mid  tri-mid  = refl
triDistribˡ tri-high tri-mid  tri-high = refl
triDistribˡ tri-high tri-high tri-low  = refl
triDistribˡ tri-high tri-high tri-mid  = refl
triDistribˡ tri-high tri-high tri-high = refl

triDistribʳ : ∀ a b c → triMul (triAdd a b) c ≡ triAdd (triMul a c) (triMul b c)
triDistribʳ tri-low  tri-low  tri-low  = refl
triDistribʳ tri-low  tri-low  tri-mid  = refl
triDistribʳ tri-low  tri-low  tri-high = refl
triDistribʳ tri-low  tri-mid  tri-low  = refl
triDistribʳ tri-low  tri-mid  tri-mid  = refl
triDistribʳ tri-low  tri-mid  tri-high = refl
triDistribʳ tri-low  tri-high tri-low  = refl
triDistribʳ tri-low  tri-high tri-mid  = refl
triDistribʳ tri-low  tri-high tri-high = refl
triDistribʳ tri-mid  tri-low  tri-low  = refl
triDistribʳ tri-mid  tri-low  tri-mid  = refl
triDistribʳ tri-mid  tri-low  tri-high = refl
triDistribʳ tri-mid  tri-mid  tri-low  = refl
triDistribʳ tri-mid  tri-mid  tri-mid  = refl
triDistribʳ tri-mid  tri-mid  tri-high = refl
triDistribʳ tri-mid  tri-high tri-low  = refl
triDistribʳ tri-mid  tri-high tri-mid  = refl
triDistribʳ tri-mid  tri-high tri-high = refl
triDistribʳ tri-high tri-low  tri-low  = refl
triDistribʳ tri-high tri-low  tri-mid  = refl
triDistribʳ tri-high tri-low  tri-high = refl
triDistribʳ tri-high tri-mid  tri-low  = refl
triDistribʳ tri-high tri-mid  tri-mid  = refl
triDistribʳ tri-high tri-mid  tri-high = refl
triDistribʳ tri-high tri-high tri-low  = refl
triDistribʳ tri-high tri-high tri-mid  = refl
triDistribʳ tri-high tri-high tri-high = refl

triInv-midˡ : triMul (triInv tri-mid) tri-mid ≡ triOne
triInv-midˡ = refl

triInv-midʳ : triMul tri-mid (triInv tri-mid) ≡ triOne
triInv-midʳ = refl

triInv-highˡ : triMul (triInv tri-high) tri-high ≡ triOne
triInv-highˡ = refl

triInv-highʳ : triMul tri-high (triInv tri-high) ≡ triOne
triInv-highʳ = refl

triNonzeroInverseReceipt : Set
triNonzeroInverseReceipt =
  (triMul (triInv tri-mid) tri-mid ≡ triOne) ×
  (triMul tri-mid (triInv tri-mid) ≡ triOne) ×
  (triMul (triInv tri-high) tri-high ≡ triOne) ×
  (triMul tri-high (triInv tri-high) ≡ triOne)

triNonzeroInverseSurface : triNonzeroInverseReceipt
triNonzeroInverseSurface =
  triInv-midˡ ,
  triInv-midʳ ,
  triInv-highˡ ,
  triInv-highʳ

record TriNoZeroDivisorReceipt : Set where
  constructor triNoZeroDivisorReceipt
  field
    low-low   : triNoZeroDivisorPairBool tri-low  tri-low  ≡ true
    low-mid   : triNoZeroDivisorPairBool tri-low  tri-mid  ≡ true
    low-high  : triNoZeroDivisorPairBool tri-low  tri-high ≡ true
    mid-low   : triNoZeroDivisorPairBool tri-mid  tri-low  ≡ true
    mid-mid   : triNoZeroDivisorPairBool tri-mid  tri-mid  ≡ true
    mid-high  : triNoZeroDivisorPairBool tri-mid  tri-high ≡ true
    high-low  : triNoZeroDivisorPairBool tri-high tri-low  ≡ true
    high-mid  : triNoZeroDivisorPairBool tri-high tri-mid  ≡ true
    high-high : triNoZeroDivisorPairBool tri-high tri-high ≡ true

triNoZeroDivisorReceiptSurface : TriNoZeroDivisorReceipt
triNoZeroDivisorReceiptSurface =
  triNoZeroDivisorReceipt
    refl refl refl
    refl refl refl
    refl refl refl

record TriTruthFieldLaws : Set where
  constructor triTruthFieldLaws
  field
    add-comm       : ∀ a b → triAdd a b ≡ triAdd b a
    add-assoc      : ∀ a b c → triAdd a (triAdd b c) ≡ triAdd (triAdd a b) c
    add-identityˡ  : ∀ a → triAdd triZero a ≡ a
    add-identityʳ  : ∀ a → triAdd a triZero ≡ a
    add-inverseˡ   : ∀ a → triAdd (triNeg a) a ≡ triZero
    add-inverseʳ   : ∀ a → triAdd a (triNeg a) ≡ triZero
    mul-comm       : ∀ a b → triMul a b ≡ triMul b a
    mul-assoc      : ∀ a b c → triMul a (triMul b c) ≡ triMul (triMul a b) c
    mul-zeroˡ      : ∀ a → triMul triZero a ≡ triZero
    mul-zeroʳ      : ∀ a → triMul a triZero ≡ triZero
    mul-identityˡ  : ∀ a → triMul triOne a ≡ a
    mul-identityʳ  : ∀ a → triMul a triOne ≡ a
    distribˡ       : ∀ a b c → triMul a (triAdd b c) ≡ triAdd (triMul a b) (triMul a c)
    distribʳ       : ∀ a b c → triMul (triAdd a b) c ≡ triAdd (triMul a c) (triMul b c)
    inverse-surface : triNonzeroInverseReceipt
    no-zero-divisor-surface : TriNoZeroDivisorReceipt

triTruthFieldLawsSurface : TriTruthFieldLaws
triTruthFieldLawsSurface =
  triTruthFieldLaws
    triAdd-comm
    triAdd-assoc
    triAdd-identityˡ
    triAdd-identityʳ
    triAdd-inverseˡ
    triAdd-inverseʳ
    triMul-comm
    triMul-assoc
    triMul-zeroˡ
    triMul-zeroʳ
    triMul-identityˡ
    triMul-identityʳ
    triDistribˡ
    triDistribʳ
    triNonzeroInverseSurface
    triNoZeroDivisorReceiptSurface
