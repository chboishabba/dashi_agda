{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPhysicalCylinderRepresentationRound499Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND499:
-- ACTUAL FINITE YM FAMILY -> COUNTABLY-ADDITIVE REPRESENTATION INPUT
--
-- R498 compiles finite normalized expectations into a projective cylinder
-- probability once event-indicator semantics + cross-cutoff consistency are
-- supplied.  R495 then needs continuity-at-empty, standard extension, and the
-- selected E_infty integral identification.
--
-- This owner composes them on the literal FinitePhysicalNormalizedFamily.
-- An unrelated abstract premeasure can no longer enter the preferred A3 route.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division
import DASHI.Physics.YangMills.YangMillsCylinderMeasureRepresentationMaxCutRound495Exact as R495
import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476

record PhysicalCylinderRepresentationInputs
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

    selectedIndex : Nat

    continuity :
      R495.ContinuityAtEmpty
        (R498.finiteEventProbability
          family
          (R498.events projectiveEvents)
          selectedIndex)

    extensionAuthority :
      R495.MeasureExtensionAuthority
        Event ℝ (Configuration → ℝ) ℝ

    sourceExpectationIsExtendedIntegral :
      ∀ observable →
      Limit.limitExpectation family observable
      ≡
      R495.integrate extensionAuthority
        (R495.extend extensionAuthority
          (R498.finiteEventProbability
            family
            (R498.events projectiveEvents)
            selectedIndex)
          continuity)
        observable

open PhysicalCylinderRepresentationInputs public

asCylinderRepresentationInputs :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family} →
  PhysicalCylinderRepresentationInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  R495.CylinderRepresentationInputs
    Nat Event ℝ (Configuration → ℝ) ℝ
    (Limit.limitExpectation family)
asCylinderRepresentationInputs inputs = record
  { R495.CylinderRepresentationInputs.projective =
      R498.asProjectiveCylinderProbability (projectiveEvents inputs)
  ; R495.CylinderRepresentationInputs.selectedIndex =
      selectedIndex inputs
  ; R495.CylinderRepresentationInputs.continuity =
      continuity inputs
  ; R495.CylinderRepresentationInputs.extensionAuthority =
      extensionAuthority inputs
  ; R495.CylinderRepresentationInputs.sourceExpectationIsExtendedIntegral =
      sourceExpectationIsExtendedIntegral inputs
  }

asSourceLimitRepresentation :
  ∀ {Configuration Event sequenceLimit limitLaws quotient division family} →
  PhysicalCylinderRepresentationInputs
    Configuration Event
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division family →
  R476.SourceLimitRepresentation
    (Configuration → ℝ)
    (Limit.limitExpectation family)
asSourceLimitRepresentation inputs =
  R495.asSourceLimitRepresentation
    (asCylinderRepresentationInputs inputs)

round499PhysicalRepresentationCompilerLevel : ProofLevel
round499PhysicalRepresentationCompilerLevel = machineChecked

round499FinitePremeasureAssemblyLevel : ProofLevel
round499FinitePremeasureAssemblyLevel =
  R498.round498FinitePremeasureCompilerLevel

round499ProjectivePremeasureAssemblyLevel : ProofLevel
round499ProjectivePremeasureAssemblyLevel =
  R498.round498ProjectivePremeasureCompilerLevel

round499MeasureExtensionCompilerLevel : ProofLevel
round499MeasureExtensionCompilerLevel =
  R495.round495RepresentationCompilerLevel

-- Preferred physical leaves after composition.
literalRound499CylinderEventIndicatorSemanticsLevel : ProofLevel
literalRound499CylinderEventIndicatorSemanticsLevel =
  R498.literalRound498CylinderEventIndicatorSemanticsLevel

literalRound499ProjectiveEventExpectationConsistencyLevel : ProofLevel
literalRound499ProjectiveEventExpectationConsistencyLevel =
  R498.literalRound498ProjectiveEventExpectationConsistencyLevel

literalRound499ContinuityAtEmptyLevel : ProofLevel
literalRound499ContinuityAtEmptyLevel =
  R495.literalRound495ContinuityAtEmptyLevel

literalRound499CylinderExpectationIdentificationLevel : ProofLevel
literalRound499CylinderExpectationIdentificationLevel =
  R495.literalRound495CylinderExpectationIdentificationLevel
