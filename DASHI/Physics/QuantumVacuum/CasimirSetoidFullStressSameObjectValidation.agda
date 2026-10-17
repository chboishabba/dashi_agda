module DASHI.Physics.QuantumVacuum.CasimirSetoidFullStressSameObjectValidation where

open import DASHI.Core.Prelude
import Data.Integer.Base as Int
open import Data.Rational.Base using (0ℚ; 1ℚ; _/_; -_)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Physics.QuantumVacuum.CasimirSetoidAnalyticScalarExact as Setoid
import DASHI.Physics.QuantumVacuum.CasimirSetoidFullStressSameObjectExact as Stress4
import DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact as Stress3
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- RED-first contract for the setoid-native full Brown-Maclay stress object.
------------------------------------------------------------------------

normalizedTimeTimeRegression :
  Stress4.normalizedSpacetimeStress Stress4.time Stress4.time
  ≡ - 1ℚ
normalizedTimeTimeRegression = refl

normalizedNormalNormalRegression :
  Stress4.normalizedSpacetimeStress
    (Stress4.space Stress3.normal)
    (Stress4.space Stress3.normal)
  ≡ - (Int.+ 3 / 1)
normalizedNormalNormalRegression = refl

normalizedTimeSpaceRegression :
  ∀ direction →
  Stress4.normalizedSpacetimeStress
    Stress4.time
    (Stress4.space direction)
  ≡ 0ℚ
normalizedTimeSpaceRegression direction = refl

setoidNormalPressureRegression :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  (scale : Stress4.CasimirSetoidScaleWitness model d) →
  Spine._≈_ (Setoid.real model)
    (Stress4.setoidNormalPressure scale)
    (Setoid.pressure model d)
setoidNormalPressureRegression =
  Stress4.setoidNormalPressureAgreesWithModel

so3NormalComponentRegression :
  ∀ {model : Setoid.CasimirSetoidScalarModel}
    {d : Q.Length} →
  (scale : Stress4.CasimirSetoidScaleWitness model d) →
  Stress4.setoidSpatialStress scale
    (Stress3.plateNormalAxis , Stress3.plateNormalAxis)
  ≡ Stress4.setoidNormalPressure scale
so3NormalComponentRegression scale = refl

sourceCitationStillNotMeasurementRegression :
  Stress4.SourceBackedStressAutomaticallyIsMeasuredStress → ⊥
sourceCitationStillNotMeasurementRegression =
  Stress4.sourceBackedStressIsNotMeasuredStress

setoidStressStillNotGRRegression :
  Stress4.SetoidQFTStressAutomaticallySolvesSemiclassicalGR → ⊥
setoidStressStillNotGRRegression =
  Stress4.setoidQFTStressDoesNotSolveGR
