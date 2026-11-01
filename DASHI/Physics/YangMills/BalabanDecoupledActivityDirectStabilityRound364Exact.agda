module DASHI.Physics.YangMills.BalabanDecoupledActivityDirectStabilityRound364Exact where

------------------------------------------------------------------------
-- ROUND364 / BYPASS R353 H_scale ON THE SOURCE-NATIVE CMP116 CARRIER
--
-- R353 reaches the R352 source theorem through the marked-walk majorant:
--
--   |H_Ω - H_Ω'| <= M_Hessian
--   M_Hessian <= L^src * d_sub^src.
--
-- Repository archaeology exposes a shorter already-owned compiler in
-- BalabanDecoupledActivityHessian.  On the literal CMP116 decoupled activity,
-- finite-polydisc Cauchy transport gives the coefficient/Hessian estimate
-- directly from:
--
--   H_local : for every boundary assignment s,
--       ||D²E(H_Ω(s)) - D²E(H_Ω'(s))||
--         <= L^src * d_sub(s)
--
--   H_subScale : d_sub(s) <= d_sub^src.
--
-- Therefore the marked-walk majorant comparison H_scale is one sufficient
-- producer tactic, not a mandatory prerequisite for R352.  This file only
-- specializes the existing theorem and packages its conclusion in the exact
-- R352 source ABI.  It does not manufacture H_local, H_subScale, or any
-- selected-carrier attachment.
--
-- Safety boundary: BalabanDecoupledActivityHessian is an older non---safe
-- donor, so this owner intentionally does not claim a --safe header.  That is
-- an import/safety coordinate, not additional YM theorem content.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact as R352
import DASHI.Physics.YangMills.BalabanSelectedHessianWalkResummationCutRound353Exact as R353

------------------------------------------------------------------------
-- Source-native direct producer data.
------------------------------------------------------------------------

record CMP116DirectSubstitutionStabilityData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData

    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    sourceLipschitz : ℝ
    sourceSubstitutionDistance : ℝ

    boundarySubstitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → ℝ

    sourceLipschitzNonnegative : 0ℝ ≤ℝ sourceLipschitz
    boundarySubstitutionDistanceNonnegative :
      ∀ s → 0ℝ ≤ℝ boundarySubstitutionDistance s
    sourceSubstitutionDistanceNonnegative :
      0ℝ ≤ℝ sourceSubstitutionDistance

    -- H_local: literal source local stability before coefficient extraction.
    boundaryHessianStable :
      ∀ s →
      Cauchy.normValue (Decoupled.cauchy decoupled)
        (Cauchy._-Value_ (Decoupled.cauchy decoupled)
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled leftDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s))
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled rightDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)))
        ≤ℝ
      sourceLipschitz *ℝ boundarySubstitutionDistance s

    -- H_subScale: literal substituted-background displacement fits the one
    -- source distance consumed by R352.
    boundarySubstitutionBelowSourceDistance :
      ∀ s → boundarySubstitutionDistance s ≤ℝ sourceSubstitutionDistance

open CMP116DirectSubstitutionStabilityData public

------------------------------------------------------------------------
-- Exact source coefficient difference and direct R352 payment.
------------------------------------------------------------------------

sourceCoefficientDifference :
  CMP116DirectSubstitutionStabilityData → ℝ
sourceCoefficientDifference dataSet =
  Cauchy.normValue (Decoupled.cauchy (decoupled dataSet))
    (Cauchy._-Value_ (Decoupled.cauchy (decoupled dataSet))
      (Decoupled.decoupledHessianCoefficient
        (decoupled dataSet)
        (leftDomain dataSet)
        (component dataSet)
        (leftVariation dataSet)
        (rightVariation dataSet))
      (Decoupled.decoupledHessianCoefficient
        (decoupled dataSet)
        (rightDomain dataSet)
        (component dataSet)
        (leftVariation dataSet)
        (rightVariation dataSet)))

directSourceHessianStability :
  (dataSet : CMP116DirectSubstitutionStabilityData) →
  sourceCoefficientDifference dataSet
    ≤ℝ sourceLipschitz dataSet *ℝ sourceSubstitutionDistance dataSet
directSourceHessianStability dataSet =
  Decoupled.markedSubstitutionStabilityLiftsToCoefficient
    (decoupled dataSet)
    (leftDomain dataSet)
    (rightDomain dataSet)
    (component dataSet)
    (leftVariation dataSet)
    (rightVariation dataSet)
    (sourceLipschitz dataSet)
    (sourceSubstitutionDistance dataSet)
    (boundarySubstitutionDistance dataSet)
    (sourceLipschitzNonnegative dataSet)
    (boundarySubstitutionDistanceNonnegative dataSet)
    (sourceSubstitutionDistanceNonnegative dataSet)
    (boundaryHessianStable dataSet)
    (boundarySubstitutionBelowSourceDistance dataSet)

round364ToR352Source :
  (dataSet : CMP116DirectSubstitutionStabilityData) →
  R352.CMP116LocalHessianStabilitySource ℝ
round364ToR352Source dataSet = record
  { sourceHessianDifference = λ _ → sourceCoefficientDifference dataSet
  ; sourceLipschitz = sourceLipschitz dataSet
  ; sourceSubstitutionDistance = λ _ → sourceSubstitutionDistance dataSet
  ; sourceHessianStable = λ _ → directSourceHessianStability dataSet
  }

------------------------------------------------------------------------
-- Pareto / route accounting.
------------------------------------------------------------------------

literalCMP116BoundaryHessianStabilityLevel : ProofLevel
literalCMP116BoundaryHessianStabilityLevel = conditional

literalCMP116SubstitutionScaleComparisonLevel : ProofLevel
literalCMP116SubstitutionScaleComparisonLevel = conditional

decoupledActivityCauchyLiftLevel : ProofLevel
decoupledActivityCauchyLiftLevel = machineChecked

round364ToR352CompilerLevel : ProofLevel
round364ToR352CompilerLevel = machineChecked

markedWalkHScaleMandatoryForR352 : Bool
markedWalkHScaleMandatoryForR352 = false

markedWalkHScaleMandatoryForR352IsFalse :
  markedWalkHScaleMandatoryForR352 ≡ false
markedWalkHScaleMandatoryForR352IsFalse = refl

markedWalkRouteStillValidOptionalProducer : Bool
markedWalkRouteStillValidOptionalProducer = true

markedWalkRouteStillValidOptionalProducerIsTrue :
  markedWalkRouteStillValidOptionalProducer ≡ true
markedWalkRouteStillValidOptionalProducerIsTrue = refl

sourceBoundaryHessianAndSubstitutionScaleAreDistinctPayments : Bool
sourceBoundaryHessianAndSubstitutionScaleAreDistinctPayments = true

sourceBoundaryHessianAndSubstitutionScaleAreDistinctPaymentsIsTrue :
  sourceBoundaryHessianAndSubstitutionScaleAreDistinctPayments ≡ true
sourceBoundaryHessianAndSubstitutionScaleAreDistinctPaymentsIsTrue = refl

r353ScaleComparisonLevelRetainedAsOptional : ProofLevel
r353ScaleComparisonLevelRetainedAsOptional =
  R353.sourceMarkedMajorantScaleComparisonLevel

record Round364Boundary : Set where
  constructor round364-boundary
  field
    boundaryHessianStabilityStillPhysical : Bool
    boundaryHessianStabilityStillPhysicalIsTrue :
      boundaryHessianStabilityStillPhysical ≡ true

    substitutionScaleComparisonStillPhysical : Bool
    substitutionScaleComparisonStillPhysicalIsTrue :
      substitutionScaleComparisonStillPhysical ≡ true

    cauchyCoefficientLiftAlreadyOwned : Bool
    cauchyCoefficientLiftAlreadyOwnedIsTrue :
      cauchyCoefficientLiftAlreadyOwned ≡ true

    r353HScaleDemotedFromMandatory : Bool
    r353HScaleDemotedFromMandatoryIsTrue :
      r353HScaleDemotedFromMandatory ≡ true

canonicalRound364Boundary : Round364Boundary
canonicalRound364Boundary =
  round364-boundary
    true refl
    true refl
    true refl
    true refl

round364FrontierRefinementLevel : ProofLevel
round364FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
