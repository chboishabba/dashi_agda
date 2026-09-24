module DASHI.Algebra.Quantum.ShorCyclicCharacterResolutionRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorCyclicCharacterResolutionExact as Resolution

------------------------------------------------------------------------
-- RED regression: one-dimensional cyclic character resolution must compile to
-- inversion of the full finite exponent x target amplitude table.
------------------------------------------------------------------------

resolutionCompilesToVectorInversion :
  ∀ {Q Coefficient}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Resolution.CyclicCharacterResolutionAuthority A →
  Vector.VectorCyclicPhaseInversionAuthority A
resolutionCompilesToVectorInversion =
  Resolution.vectorInversionFromCharacterResolution
