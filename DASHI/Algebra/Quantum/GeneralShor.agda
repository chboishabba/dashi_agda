module DASHI.Algebra.Quantum.GeneralShor where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Quantum.FiniteQuantumRegister
open import DASHI.Algebra.Quantum.QuantumFourierTransformFinite
open import DASHI.Crypto.FiniteFactorArithmetic using (Positive)

------------------------------------------------------------------------
-- General Shor surface: finite abelian hidden-subgroup / period finding.
------------------------------------------------------------------------

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    to : A → B
    from : B → A

open _↔_ public

record FiniteAbelianHiddenSubgroupProblem : Set₁ where
  field
    Element : Set
    Observation : Set
    enumerate : List Element

    unit : Element
    _∙_ : Element → Element → Element
    inverse : Element → Element

    associative : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
    unitLeft : ∀ x → unit ∙ x ≡ x
    unitRight : ∀ x → x ∙ unit ≡ x
    inverseLeft : ∀ x → inverse x ∙ x ≡ unit
    commutative : ∀ x y → x ∙ y ≡ y ∙ x

    Hidden : Element → Set
    hiddenUnit : Hidden unit
    hiddenClosed : ∀ {x y} → Hidden x → Hidden y → Hidden (x ∙ y)
    hiddenInverse : ∀ {x} → Hidden x → Hidden (inverse x)

    oracle : Element → Observation
    sameCoset : Element → Element → Set
    sameCosetLaw :
      ∀ x y →
      (oracle x ≡ oracle y) ↔ sameCoset x y

open FiniteAbelianHiddenSubgroupProblem public

record GeneralShorMachine
    (H : FiniteAbelianHiddenSubgroupProblem) : Set₁ where
  field
    basis : FiniteBasis
    register : FiniteQuantumRegister basis
    fourierTransform : FiniteFourierTransform register

    Sample : Set
    execute : Nat → Sample
    successful : Sample → Set

    RecoveredInvariant : Set
    recover : Sample → RecoveredInvariant
    invariantCorrect : RecoveredInvariant → Set

    successfulRecovery :
      ∀ seed →
      successful (execute seed) →
      invariantCorrect (recover (execute seed))

open GeneralShorMachine public

record HiddenPeriodProblem : Set₁ where
  field
    Value : Set
    oracle : Nat → Value
    period : Nat
    periodPositive : Positive period

    periodic :
      ∀ x → oracle (x + period) ≡ oracle x

    exactPeriod :
      ∀ k →
      Positive k →
      k < period →
      ¬ (∀ x → oracle (x + k) ≡ oracle x)

open HiddenPeriodProblem public

record ShorPeriodFindingMachine (H : HiddenPeriodProblem) : Set₁ where
  field
    basis : FiniteBasis
    register : FiniteQuantumRegister basis
    fourierTransform : FiniteFourierTransform register

    Sample : Set
    execute : Nat → Sample
    successful : Sample → Set
    recoverPeriod : Sample → Nat

    successfulRecovery :
      ∀ seed →
      successful (execute seed) →
      recoverPeriod (execute seed) ≡ period H

open ShorPeriodFindingMachine public

record ShorSuccessEvidence
    {H : HiddenPeriodProblem}
    (M : ShorPeriodFindingMachine H) : Set₁ where
  field
    seed : Nat
    success : successful M (execute M seed)

open ShorSuccessEvidence public

recoveredPeriodIsExact :
  {H : HiddenPeriodProblem} →
  (M : ShorPeriodFindingMachine H) →
  (E : ShorSuccessEvidence M) →
  recoverPeriod M (execute M (seed E)) ≡ period H
recoveredPeriodIsExact M E = successfulRecovery M (seed E) (success E)

record ShorProbabilityEvidence
    {H : HiddenPeriodProblem}
    (M : ShorPeriodFindingMachine H) : Set₁ where
  field
    Probability : Set
    successProbability : Probability
    lowerBound : Probability
    _≤P_ : Probability → Probability → Set
    certifiedLowerBound : lowerBound ≤P successProbability

open ShorProbabilityEvidence public
