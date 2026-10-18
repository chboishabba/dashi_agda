module DASHI.Crypto.ShorCanonicalCoefficientSupportRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Crypto.ShorFiniteVectorSupportedObservationExact as Supported
import DASHI.Crypto.ShorCanonicalCoefficientSupportExact as Canonical

------------------------------------------------------------------------
-- RED regression.
--
-- Preferred support semantics must not be a caller-selected predicate.  A
-- coefficient is supported exactly when it is propositionally unequal to the
-- coefficient zero supplied by the literal cyclic-QFT algebra.
------------------------------------------------------------------------

canonicalNonzeroMeansNotZero :
  ∀ {Q Coefficient}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    (coefficient : Coefficient) →
  Supported.NonzeroCoefficient (Canonical.canonicalCoefficientSupport A) coefficient
  ≡ (coefficient ≡ Phase.zeroCoefficient A → ⊥)
canonicalNonzeroMeansNotZero coefficient = refl
