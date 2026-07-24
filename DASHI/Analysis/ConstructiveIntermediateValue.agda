module DASHI.Analysis.ConstructiveIntermediateValue where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConstructiveSeries
open import DASHI.Analysis.PowerSeriesTranscendentals

------------------------------------------------------------------------
-- Constructive continuity and interval roots.

record ContinuousOnInterval
  (R : ConstructedOrderedCompleteReal)
  (f : Real R → Real R)
  (left right : Real R) : Set₁ where
  field
    modulus : Real R → Real R
    ModulusAdmissible : Set
    continuityEstimate : Set

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
-- Exponential surjectivity.  The range theorem supplies finite brackets for
-- each positive target; IVT supplies existence and strict monotonicity supplies
-- uniqueness through the existing exponential package.

record ExponentialRangeAndContinuity
  (R : ConstructedOrderedCompleteReal)
  (exp : Real R → Real R)
  (Positive : Real R → Set) : Set₁ where
  field
    bracket :
      ∀ y → Positive y →
      Σ (Real R)
        (λ left →
          Σ (Real R)
            (λ right →
              Σ (_≤_ R left right)
                (λ _ →
                  Σ Set
                    (λ ExpLeftBelowTarget →
                      Σ Set
                        (λ TargetBelowExpRight → Set)))))

    ExpLeftBelowTarget : ∀ y py → Set
    TargetBelowExpRight : ∀ y py → Set

    bracketLeftCondition : ∀ y py → ExpLeftBelowTarget y py
    bracketRightCondition : ∀ y py → TargetBelowExpRight y py

    shiftedExponential : Real R → Real R → Real R
    shiftedDefinition : ∀ y x →
      shiftedExponential y x ≡ _-_ R (exp x) y

    shiftedContinuous : ∀ y py →
      let left = fst (bracket y py)
          right = fst (snd (bracket y py))
      in ContinuousOnInterval R (shiftedExponential y) left right

open ExponentialRangeAndContinuity public

record ExponentialIVTCompatibility
  (R : ConstructedOrderedCompleteReal)
  (I : IntermediateValueAuthority R)
  (exp : Real R → Real R)
  (Positive : Real R → Set)
  (A : ExponentialRangeAndContinuity R exp Positive) : Set₁ where
  field
    leftSign : ∀ y py →
      let left = fst (bracket A y py)
      in Nonpositive I (shiftedExponential A y left)

    rightSign : ∀ y py →
      let right = fst (snd (bracket A y py))
      in Nonnegative I (shiftedExponential A y right)

    shiftedZeroImpliesExpEquals : ∀ y x →
      shiftedExponential A y x ≡ zero R →
      exp x ≡ y

open ExponentialIVTCompatibility public

expOntoPositiveFromIVT :
  ∀ {R : ConstructedOrderedCompleteReal}
    (I : IntermediateValueAuthority R)
    (exp : Real R → Real R)
    (Positive : Real R → Set)
    (A : ExponentialRangeAndContinuity R exp Positive) →
  ExponentialIVTCompatibility R I exp Positive A →
  ∀ y → Positive y → Σ (Real R) (λ x → exp x ≡ y)
expOntoPositiveFromIVT {R} I exp Positive A C y py =
  root , shiftedZeroImpliesExpEquals C y root rootZero
  where
    left : Real R
    left = fst (bracket A y py)

    right : Real R
    right = fst (snd (bracket A y py))

    left≤right : _≤_ R left right
    left≤right = fst (snd (snd (bracket A y py)))

    rootReceipt :
      Σ (Real R)
        (λ root →
          Σ (_≤_ R left root)
            (λ _ →
              Σ (_≤_ R root right)
                (λ _ → shiftedExponential A y root ≡ zero R)))
    rootReceipt =
      rootBetween I
        (shiftedExponential A y)
        left
        right
        left≤right
        (shiftedContinuous A y py)
        (leftSign C y py)
        (rightSign C y py)

    root : Real R
    root = fst rootReceipt

    rootZero : shiftedExponential A y root ≡ zero R
    rootZero = snd (snd (snd rootReceipt))

------------------------------------------------------------------------
-- First positive zero of cosine.  IVT proves existence from one sign-changing
-- interval; a separate positivity-before theorem proves that the chosen zero is
-- the first one and therefore supports the definition pi = 2 * halfPi.

record CosineSignChange
  (R : ConstructedOrderedCompleteReal)
  (cosine : Real R → Real R)
  (I : IntermediateValueAuthority R) : Set₁ where
  field
    left right : Real R
    leftPositive : _<_ R (zero R) left
    left≤right : _≤_ R left right
    cosineContinuous : ContinuousOnInterval R cosine left right
    cosineLeftNonnegative : Nonnegative I (cosine left)
    cosineRightNonpositive : Nonpositive I (cosine right)

open CosineSignChange public

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
firstPositiveCosineZeroFromMinimality M =
  record
    { halfPi = _
    ; halfPiPositive = halfPiPositive M
    ; cosineHalfPiZero = cosineHalfPiZero M
    ; cosinePositiveBefore = cosinePositiveBefore M
    }
