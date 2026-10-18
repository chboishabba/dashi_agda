{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralRealCylinderLimitPhysicalMeasureExact where

------------------------------------------------------------------------
-- NORMALIZED REAL CMP119 CYLINDER LIMIT -> LITERAL PHYSICAL CONTINUUM MEASURE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; 1ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Normalized
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

literalRealContinuumMeasure :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division) →
  Physical.PhysicalContinuumYMMeasure Observable ℝ
literalRealContinuumMeasure source =
  Physical.physicalContinuumMeasure
    (Normalized.continuumNormalized source)

literalRealContinuumExpectation :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division) →
  Observable → ℝ
literalRealContinuumExpectation source =
  Physical.expectation
    (literalRealContinuumMeasure source)

literalRealContinuumExpectationIsNormalizedLimit :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division)
    observable →
  literalRealContinuumExpectation source observable
  ≡
  Normalized.continuumNormalized source observable
literalRealContinuumExpectationIsNormalizedLimit source observable = refl

literalRealFiniteExpectationConverges :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division)
    observable →
  Cylinder.Converges algebra
    (λ n → Normalized.finiteNormalized source n observable)
    (literalRealContinuumExpectation source observable)
literalRealFiniteExpectationConverges source observable =
  Normalized.normalizedConverges source observable

literalRealContinuumMeasureNormalized :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division) →
  literalRealContinuumExpectation source
    (Normalized.oneObservable source)
  ≡ 1ℝ
literalRealContinuumMeasureNormalized source =
  Cylinder.limitOne
    (Normalized.asScalarCylinderExpectationLimitData source)

literalRealContinuumMeasurePositive :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division)
    observable →
  Normalized.Nonnegative source observable →
  0ℝ ≤ℝ literalRealContinuumExpectation source observable
literalRealContinuumMeasurePositive source observable nonnegative =
  Cylinder.limitPositive
    (Normalized.asScalarCylinderExpectationLimitData source)
    observable nonnegative

literalRealCylinderPhysicalMeasureCompilerLevel : ProofLevel
literalRealCylinderPhysicalMeasureCompilerLevel = machineChecked

-- The literal A residual is now analytic:
-- produce the normalized source package from the actual CMP119/Haar family,
-- then prove the same measure's Schwinger/OS reconstruction properties.
literalCMP119NormalizedCylinderSourceLevel : ProofLevel
literalCMP119NormalizedCylinderSourceLevel = conditional

literalRealContinuumOSLevel : ProofLevel
literalRealContinuumOSLevel = conditional
