{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND535:
-- ACTUAL FINITE YM FAMILY -> WHOLE-PROJECTIVE CONTINUUM REPRESENTATION
--
-- Compose:
--
--   literal FinitePhysicalNormalizedFamily
--     -> R498 projective cylinder probabilities
--     -> R534 whole-projective extension
--     -> represented countably-additive continuum measure.
--
-- There is no selected finite cutoff in this preferred constructor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PhysicalProjectiveCylinderRepresentationInputs
    (Configuration Event : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    : Set₂ where
  field
    projectiveEvents :
      R498.ProjectiveCylinderEventInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division family

    continuity :
      R534.ProjectiveContinuityAtEmpty
        (R498.asProjectiveCylinderProbability projectiveEvents)

    extensionAuthority :
      R534.ProjectiveMeasureExtensionAuthority
        Nat Event ℝ (Configuration → ℝ) ℝ

    -- Ensure the standard extension theorem's cylinder indicators are the SAME
    -- literal event indicators used to define finite YM probabilities.
    extensionIndicatorIsLiteralIndicator :
      ∀ cutoff event →
      R534.indicatorAt extensionAuthority cutoff event
      ≡ R498.indicator (R498.events projectiveEvents) event

    sourceExpectationIsExtendedIntegral :
      ∀ observable →
      Limit.limitExpectation family observable
      ≡
      R534.integrate extensionAuthority
        (R534.extendProjective extensionAuthority
          (R498.asProjectiveCylinderProbability projectiveEvents)
          continuity)
        observable

open PhysicalProjectiveCylinderRepresentationInputs public

asProjectiveRepresentationInputs :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family} →
  PhysicalProjectiveCylinderRepresentationInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  R534.ProjectiveCylinderRepresentationInputs
    Nat Event ℝ (Configuration → ℝ) ℝ
    (Limit.limitExpectation family)
asProjectiveRepresentationInputs inputs = record
  { R534.ProjectiveCylinderRepresentationInputs.projective =
      R498.asProjectiveCylinderProbability (projectiveEvents inputs)
  ; R534.ProjectiveCylinderRepresentationInputs.continuity =
      continuity inputs
  ; R534.ProjectiveCylinderRepresentationInputs.extensionAuthority =
      extensionAuthority inputs
  ; R534.ProjectiveCylinderRepresentationInputs.sourceExpectationIsExtendedIntegral =
      sourceExpectationIsExtendedIntegral inputs
  }

asSourceLimitRepresentation :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family} →
  PhysicalProjectiveCylinderRepresentationInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  R476.SourceLimitRepresentation
    (Configuration → ℝ)
    (Limit.limitExpectation family)
asSourceLimitRepresentation inputs =
  R534.asSourceLimitRepresentation
    (asProjectiveRepresentationInputs inputs)

round535PhysicalProjectiveRepresentationCompilerLevel : ProofLevel
round535PhysicalProjectiveRepresentationCompilerLevel = machineChecked

round535FiniteProjectivePremeasureCompilerLevel : ProofLevel
round535FiniteProjectivePremeasureCompilerLevel =
  R498.round498ProjectivePremeasureCompilerLevel

literalRound535CylinderEventIndicatorSemanticsLevel : ProofLevel
literalRound535CylinderEventIndicatorSemanticsLevel =
  R498.literalRound498CylinderEventIndicatorSemanticsLevel

literalRound535ProjectiveEventExpectationConsistencyLevel : ProofLevel
literalRound535ProjectiveEventExpectationConsistencyLevel =
  R498.literalRound498ProjectiveEventExpectationConsistencyLevel

literalRound535ProjectiveContinuityAtEmptyLevel : ProofLevel
literalRound535ProjectiveContinuityAtEmptyLevel =
  R534.literalRound534ProjectiveContinuityAtEmptyLevel

literalRound535CylinderExpectationIntegralIdentificationLevel : ProofLevel
literalRound535CylinderExpectationIntegralIdentificationLevel =
  R534.literalRound534SourceExpectationIntegralIdentificationLevel

selectedIndexRepresentationStillPreferred : Bool
selectedIndexRepresentationStillPreferred = false
