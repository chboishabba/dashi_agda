{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralFixedPointMetricHessianRound383Exact where

------------------------------------------------------------------------
-- ROUND383 / LITERAL R103 HESSIAN ON THE R370 FIXED-POINT METRIC
--
-- R382 removed the duplicate R372/R370 distance coordinate by measuring the
-- Hessian Cauchy family in the exact R370 fixed-point-output metric.  Its generic
-- compiler still allowed an arbitrary Hessian family and arbitrary scalar
-- difference.
--
-- Round375 already established the correct physical family: the selected
-- Hessian is definitionally the R103 literal CMP116 marked Hessian,
--
--   background |-> cmp116PhysicalMarkedHessian background u v.
--
-- This owner specializes R382 to that literal family and chooses the scalar
-- difference to BE the exact R373 boundary norm difference.  Therefore two more
-- representation coordinates disappear by construction:
--
--   * no free Hessian-family identity;
--   * no separate Hessian-difference = boundary-norm weld.
--
-- The only surviving scalarization theorem is the genuine one:
--
--   literal R373 boundary norm
--     = Hessian-target distance between the two R103 literal Hessian values.
--
-- Quantitative analyticity, magnitude/radius and common-neighbourhood payments
-- remain source/application inputs; this module does not fabricate them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as R103
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116ParametricDistanceUpperHessianRound380Exact as R380
import DASHI.Physics.YangMills.BalabanCMP116FixedPointMetricHessianRound382Exact as R382

record LiteralFixedPointMetricHessianData : Set₁ where
  field
    parametric : R370.CMP116DirectParametricSensitivityData
    literal : R103.LiteralDifferentiatedEffectiveDensityCarrier

    -- Same physical background carrier.  Keeping this as a type equality field
    -- would force transport through Set equality; instead the application gives
    -- the actual selected left/right R103 backgrounds below and proves they are
    -- the same objects as the R370 fixed-point outputs through one embedding.
    toLiteralBackground :
      R370.Background parametric →
      Source.Background (R103.source literal)

    leftVariation rightVariation :
      R380.R370Boundary parametric →
      Source.Tangent (R103.source literal)

    hessianAuthority :
      R382.HessianCauchyOnR370FixedPointMetric parametric ℝ

    sourceMagnitudeBound sourceRadius : ℝ

    sourceHessianAnalytic :
      ∀ s →
      R382.AnalyticFamily hessianAuthority
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal
            (toLiteralBackground background)
            (leftVariation s) (rightVariation s))

    sourceHessianUniformlyBounded :
      ∀ s →
      R382.UniformMagnitudeBound hessianAuthority
        (λ background →
          R103.cmp116PhysicalMarkedHessian literal
            (toLiteralBackground background)
            (leftVariation s) (rightVariation s))
        sourceMagnitudeBound

    sourceRadiusPositive :
      R382.PositiveRadiusMargin hessianAuthority sourceRadius

    selectedSubstitutedBackgroundsShareNeighbourhood :
      ∀ s →
      R382.CommonNeighbourhood hessianAuthority
        (R382.leftFixedPoint
          (record
            { R382.parametric = parametric
            ; R382.HessianValue = ℝ
            ; R382.hessianAuthority = hessianAuthority
            ; R382.hessianFamily = λ _ background → 0ℝ
            ; R382.sourceMagnitudeBound = sourceMagnitudeBound
            ; R382.sourceRadius = sourceRadius
            ; R382.sourceHessianAnalytic = λ _ → sourceHessianAnalytic s
            ; R382.sourceHessianUniformlyBounded = λ _ → sourceHessianUniformlyBounded s
            ; R382.sourceRadiusPositive = sourceRadiusPositive
            ; R382.selectedSubstitutedBackgroundsShareNeighbourhood = λ _ → selectedSubstitutedBackgroundsShareNeighbourhood s
            ; R382.sourceHessianDifference = λ _ → 0ℝ
            ; R382.sourceHessianDifferenceIsTargetDistance = λ _ → refl
            ; R382.hessianDifferenceIsBoundaryNorm = λ _ → refl
            ; R382.sourceHessianLipschitzNonnegative = ≤ℝ-refl
            }) s)
        (R382.rightFixedPoint
          (record
            { R382.parametric = parametric
            ; R382.HessianValue = ℝ
            ; R382.hessianAuthority = hessianAuthority
            ; R382.hessianFamily = λ _ background → 0ℝ
            ; R382.sourceMagnitudeBound = sourceMagnitudeBound
            ; R382.sourceRadius = sourceRadius
            ; R382.sourceHessianAnalytic = λ _ → sourceHessianAnalytic s
            ; R382.sourceHessianUniformlyBounded = λ _ → sourceHessianUniformlyBounded s
            ; R382.sourceRadiusPositive = sourceRadiusPositive
            ; R382.selectedSubstitutedBackgroundsShareNeighbourhood = λ _ → selectedSubstitutedBackgroundsShareNeighbourhood s
            ; R382.sourceHessianDifference = λ _ → 0ℝ
            ; R382.sourceHessianDifferenceIsTargetDistance = λ _ → refl
            ; R382.hessianDifferenceIsBoundaryNorm = λ _ → refl
            ; R382.sourceHessianLipschitzNonnegative = ≤ℝ-refl
            }) s)

    -- The one surviving scalarization theorem.
    boundaryNormIsLiteralHessianTargetDistance :
      ∀ s →
      R373.boundaryNormDifference
        (R370.decoupled parametric)
        (R370.leftDomain parametric)
        (R370.rightDomain parametric)
        (R370.component parametric)
        (R370.leftVariation parametric)
        (R370.rightVariation parametric)
        s
      ≡
      R382.hessianDistance hessianAuthority
        (R103.cmp116PhysicalMarkedHessian literal
          (toLiteralBackground
            (R370.fixedPointFamily parametric
              (R370.boundaryIndex parametric s)
              (R370.leftParameter parametric
                (R370.boundaryIndex parametric s))))
          (leftVariation s) (rightVariation s))
        (R103.cmp116PhysicalMarkedHessian literal
          (toLiteralBackground
            (R370.fixedPointFamily parametric
              (R370.boundaryIndex parametric s)
              (R370.rightParameter parametric
                (R370.boundaryIndex parametric s))))
          (leftVariation s) (rightVariation s))

    sourceHessianLipschitzNonnegative :
      0ℝ ≤ℝ
      R382.lipschitzConstant hessianAuthority sourceMagnitudeBound sourceRadius

open LiteralFixedPointMetricHessianData public

------------------------------------------------------------------------
-- NOTE
--
-- The giant-looking CommonNeighbourhood field above is intentionally NOT the
-- final implementation shape.  It exposes a source-level dependency cycle if we
-- try to define R382.leftFixedPoint through an already-completed R382 record.
-- The useful result of this source write is therefore diagnostic: the literal
-- specialization should define the left/right fixed-point values locally, just
-- as R382 does, and consume the neighbourhood theorem directly.  Until that
-- simplification is made, this owner is not wired into validation and carries no
-- machineChecked status.
------------------------------------------------------------------------

round383DraftExposesNeighbourhoodSelfReference : Bool
round383DraftExposesNeighbourhoodSelfReference = true

round383DraftExposesNeighbourhoodSelfReferenceIsTrue :
  round383DraftExposesNeighbourhoodSelfReference ≡ true
round383DraftExposesNeighbourhoodSelfReferenceIsTrue = refl

round383PromotedCompiler : Bool
round383PromotedCompiler = false

round383PromotedCompilerIsFalse : round383PromotedCompiler ≡ false
round383PromotedCompilerIsFalse = refl
