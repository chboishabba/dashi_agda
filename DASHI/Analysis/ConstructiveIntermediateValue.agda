module DASHI.Analysis.ConstructiveIntermediateValue where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.PowerSeriesTranscendentals

------------------------------------------------------------------------
-- Constructive continuity and interval roots.

record ContinuousOnInterval
  (R : ConstructedOrderedCompleteReal)
  (f : Real R → Real R)
  (left right : Real R) : Set₁ where
  field
    Modulus : Set
    modulus : Modulus
    ContinuityEstimate : Set
    continuityEstimate : ContinuityEstimate

open ContinuousOnInterval public

record IntermediateValueAuthority
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    Nonnegative Nonpositive : Real R → Set

    rootBetween :
      ∀ (f : Real R → Real R) left right →
      _≤_ R left right →
      ContinuousOnInterval R f left right →
      Nonpositive (f left) →
      Nonnegative (f right) →
      Σ (Real R)
        (λ root →
          Σ (_≤_ R left root)
            (λ _ →
              Σ (_≤_ R root right)
                (λ _ → f root ≡ zero R)))

open IntermediateValueAuthority public

------------------------------------------------------------------------
-- Exponential surjectivity.  For every positive target, the range theorem
-- supplies a finite interval on which exp(x)-y changes sign.  IVT supplies the
-- preimage; injectivity is used later by the logarithm constructor.

record ExponentialBracket
  (R : ConstructedOrderedCompleteReal)
  (I : IntermediateValueAuthority R)
  (shifted : Real R → Real R)
  : Set₁ where
  field
    left right : Real R
    left≤right : _≤_ R left right
    continuous : ContinuousOnInterval R shifted left right
    leftNonpositive : Nonpositive I (shifted left)
    rightNonnegative : Nonnegative I (shifted right)

open ExponentialBracket public

record ExponentialRangeAndContinuity
  (R : ConstructedOrderedCompleteReal)
  (I : IntermediateValueAuthority R)
  (exp : Real R → Real R)
  (Positive : Real R → Set) : Set₁ where
  field
    shiftedExponential : Real R → Real R → Real R
    shiftedZeroImpliesExpEquals : ∀ y x →
      shiftedExponential y x ≡ zero R →
      exp x ≡ y

    bracket : ∀ y → Positive y →
      ExponentialBracket R I (shiftedExponential y)

open ExponentialRangeAndContinuity public

expOntoPositiveFromIVT :
  ∀ {R : ConstructedOrderedCompleteReal}
    (I : IntermediateValueAuthority R)
    (exp : Real R → Real R)
    (Positive : Real R → Set) →
  (A : ExponentialRangeAndContinuity R I exp Positive) →
  ∀ y → Positive y → Σ (Real R) (λ x → exp x ≡ y)
expOntoPositiveFromIVT {R} I exp Positive A y py =
  root , shiftedZeroImpliesExpEquals A y root rootZero
  where
    B : ExponentialBracket R I (shiftedExponential A y)
    B = bracket A y py

    rootReceipt :
      Σ (Real R)
        (λ root →
          Σ (_≤_ R (left B) root)
            (λ _ →
              Σ (_≤_ R root (right B))
                (λ _ → shiftedExponential A y root ≡ zero R)))
    rootReceipt =
      rootBetween I
        (shiftedExponential A y)
        (left B)
        (right B)
        (left≤right B)
        (continuous B)
        (leftNonpositive B)
        (rightNonnegative B)

    root : Real R
    root = fst rootReceipt

    rootZero : shiftedExponential A y root ≡ zero R
    rootZero = snd (snd (snd rootReceipt))

------------------------------------------------------------------------
-- First positive zero of cosine.  An IVT sign-change proof supplies a zero;
-- the minimality theorem below is the exact extra fact needed to call it π/2.

record FirstZeroMinimality
  (R : ConstructedOrderedCompleteReal)
  (cosine : Real R → Real R)
  (halfPi : Real R) : Set₁ where
  field
    halfPiPositive : _<_ R (zero R) halfPi
    cosineHalfPiZero : cosine halfPi ≡ zero R
    cosinePositiveBefore : ∀ x →
      _<_ R (zero R) x →
      _<_ R x halfPi →
      _<_ R (zero R) (cosine x)

open FirstZeroMinimality public

firstPositiveCosineZeroFromMinimality :
  ∀ {R : ConstructedOrderedCompleteReal}
    {cosine : Real R → Real R}
    {halfPi : Real R} →
  FirstZeroMinimality R cosine halfPi →
  FirstPositiveCosineZero R cosine
firstPositiveCosineZeroFromMinimality {halfPi = halfPi} M =
  record
    { halfPi = halfPi
    ; halfPiPositive = halfPiPositive M
    ; cosineHalfPiZero = cosineHalfPiZero M
    ; cosinePositiveBefore = cosinePositiveBefore M
    }
