module DASHI.Crypto.ShorCanonicalCoefficientSupportExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported

------------------------------------------------------------------------
-- CANONICAL COEFFICIENT SUPPORT
--
-- The preferred Shor route does not need an arbitrary support predicate.
-- Given the coefficient zero already owned by the literal cyclic-QFT algebra,
-- define support canonically as propositional inequality to that zero:
--
--     supported(c) := c ≠ 0.
--
-- This requires no decidable equality, probability measure, norm, ordering or
-- analytic structure.  It is only the weakest constructive nonzero statement
-- needed by the supported-outcome ABI.
------------------------------------------------------------------------

canonicalCoefficientSupport :
  ∀ {Q Coefficient} →
  (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Supported.CoefficientSupportAuthority A
canonicalCoefficientSupport A =
  Supported.coefficientSupportAuthority
    (λ coefficient → coefficient ≡ Phase.zeroCoefficient A → ⊥)
    (λ zeroIsNonzero → zeroIsNonzero refl)

canonicalSupportIsNotZero :
  ∀ {Q Coefficient}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    (coefficient : Coefficient) →
  Supported.NonzeroCoefficient (canonicalCoefficientSupport A) coefficient
  ≡ (coefficient ≡ Phase.zeroCoefficient A → ⊥)
canonicalSupportIsNotZero coefficient = refl

record ShorCanonicalCoefficientSupportBoundary : Set where
  constructor shorCanonicalCoefficientSupportBoundary
  field
    supportPredicateCallerChosen : Bool
    supportMeansPropositionalNotZero : Bool
    decidableEqualityRequired : Bool
    coefficientNormRequired : Bool
    probabilityMeasureRequired : Bool

canonicalShorCanonicalCoefficientSupportBoundary :
  ShorCanonicalCoefficientSupportBoundary
canonicalShorCanonicalCoefficientSupportBoundary =
  shorCanonicalCoefficientSupportBoundary
    false true false false false
