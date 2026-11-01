module DASHI.Education.DigitalESDEligibilityFrameExclusionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Core.ParticipationSelectionQuotient as Selection
import DASHI.Core.ReopenableProjectionComposition as Reopenable
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design

------------------------------------------------------------------------
-- DIGITAL-ESD ELIGIBILITY-FRAME EXCLUSION
--
-- Existing repo donors:
--   * ParticipationSelectionQuotient separates eligibility, invitation and
--     realised participation before expression.
--   * EvidenceDesignAdmissibilityExact retains samplingFrame as a first-class
--     study-design coordinate.
--
-- This owner moves one level upstream.  It asks whether the declared eligible
-- carrier itself can recover people excluded by eligibility-definition,
-- administrative-register or recruitment-frame construction.
--
-- The finite collision below is DASHI-owned.  It is not an empirical result
-- attributed to any external source.
------------------------------------------------------------------------

selectionPipelineDonor : Reopenable.ExactReopenableProjection Selection.PopulationState Selection.ParticipatingSurface
selectionPipelineDonor = Selection.populationToParticipating

samplingFrameCoordinateReading : String
samplingFrameCoordinateReading =
  "EvidenceDesignAdmissibilityExact owns samplingFrame as a study-design coordinate; this module does not redefine that design vocabulary."

------------------------------------------------------------------------
-- Upstream frame state.
------------------------------------------------------------------------

data EligibilityFrameWorld : Set where
  sameEligibleCarrierBroadFrame : EligibilityFrameWorld
  sameEligibleCarrierNarrowFrame : EligibilityFrameWorld

data DeclaredEligibleCarrier : Set where
  sameDeclaredEligibleCarrier : DeclaredEligibleCarrier

data EligibilityFrameState : Set where
  broadAdministrativeAndRecruitmentFrame : EligibilityFrameState
  narrowAdministrativeOrRecruitmentFrame : EligibilityFrameState

declaredEligibleProjection : EligibilityFrameWorld → DeclaredEligibleCarrier
declaredEligibleProjection sameEligibleCarrierBroadFrame = sameDeclaredEligibleCarrier
declaredEligibleProjection sameEligibleCarrierNarrowFrame = sameDeclaredEligibleCarrier

eligibilityFrameState : EligibilityFrameWorld → EligibilityFrameState
eligibilityFrameState sameEligibleCarrierBroadFrame = broadAdministrativeAndRecruitmentFrame
eligibilityFrameState sameEligibleCarrierNarrowFrame = narrowAdministrativeOrRecruitmentFrame

frameStatesDiffer :
  eligibilityFrameState sameEligibleCarrierBroadFrame ≡
  eligibilityFrameState sameEligibleCarrierNarrowFrame → ⊥
frameStatesDiffer ()

eligibilityFrameWitness :
  Intersection.NonFactorabilityWitness declaredEligibleProjection eligibilityFrameState
eligibilityFrameWitness =
  Intersection.nonFactorabilityWitness
    sameEligibleCarrierBroadFrame
    sameEligibleCarrierNarrowFrame
    refl
    frameStatesDiffer

EligibilityFrameFactorisation : Set₁
EligibilityFrameFactorisation =
  Intersection.FactorsThrough declaredEligibleProjection eligibilityFrameState

eligibilityFrameDoesNotFactorThroughDeclaredEligibleCarrier :
  EligibilityFrameFactorisation → ⊥
eligibilityFrameDoesNotFactorThroughDeclaredEligibleCarrier =
  Intersection.witnessRulesOutEveryFlatFactorisation eligibilityFrameWitness

------------------------------------------------------------------------
-- Consumer-relative probes.
------------------------------------------------------------------------

data EligibilityFrameProbe : Set where
  inspectEligibilityDefinition : EligibilityFrameProbe
  inspectAdministrativeRegisterCoverage : EligibilityFrameProbe
  inspectRecruitmentFrame : EligibilityFrameProbe

probeReading : EligibilityFrameProbe → String
probeReading inspectEligibilityDefinition =
  "inspect which substantive or administrative rules define membership in the declared eligible population"
probeReading inspectAdministrativeRegisterCoverage =
  "inspect who belongs to the target population but is absent from the administrative register or denominator used to construct eligibility"
probeReading inspectRecruitmentFrame =
  "inspect who is substantively eligible but unreachable or excluded by the recruitment, invitation, language, address, platform, documentation or contact frame"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DeclaredEligibleCreatesTargetUniverse : Set where
data SamplingFrameCreatesPopulationTruth : Set where
data RecruitmentFrameCreatesCoverageTruth : Set where
data FrameExclusionCreatesHarmVerdict : Set where

declaredEligibleDoesNotCreateTargetUniverse :
  DeclaredEligibleCreatesTargetUniverse → ⊥
declaredEligibleDoesNotCreateTargetUniverse ()

samplingFrameDoesNotCreatePopulationTruth :
  SamplingFrameCreatesPopulationTruth → ⊥
samplingFrameDoesNotCreatePopulationTruth ()

recruitmentFrameDoesNotCreateCoverageTruth :
  RecruitmentFrameCreatesCoverageTruth → ⊥
recruitmentFrameDoesNotCreateCoverageTruth ()

frameExclusionDoesNotCreateHarmVerdict :
  FrameExclusionCreatesHarmVerdict → ⊥
frameExclusionDoesNotCreateHarmVerdict ()

------------------------------------------------------------------------
-- Boundary / reading.
------------------------------------------------------------------------

record EligibilityFrameBoundary : Set where
  constructor eligibility-frame-boundary
  field
    eligibilityDistinctFromParticipation : Bool
    eligibilityDistinctFromParticipationIsTrue :
      eligibilityDistinctFromParticipation ≡ true
    samplingFrameRetainedAsDesignCoordinate : Bool
    samplingFrameRetainedAsDesignCoordinateIsTrue :
      samplingFrameRetainedAsDesignCoordinate ≡ true
    declaredEligibilityRecoversUpstreamFrame : Bool
    declaredEligibilityRecoversUpstreamFrameIsFalse :
      declaredEligibilityRecoversUpstreamFrame ≡ false
    frameExclusionCreatesAutomaticHarmVerdict : Bool
    frameExclusionCreatesAutomaticHarmVerdictIsFalse :
      frameExclusionCreatesAutomaticHarmVerdict ≡ false

open EligibilityFrameBoundary public

canonicalEligibilityFrameBoundary : EligibilityFrameBoundary
canonicalEligibilityFrameBoundary = eligibility-frame-boundary
  true refl
  true refl
  false refl
  false refl

eligibilityFrameReading : String
eligibilityFrameReading =
  "Digital-ESD now distinguishes the target universe, eligibility-definition / administrative-register / recruitment frame, declared eligible carrier, invitation/participation gates and realised analytic carrier. The same declared eligible surface can coexist with different upstream frame exclusions, so EligibilityFrameState does not factor through DeclaredEligibleCarrier. ParticipationSelectionQuotient and EvidenceDesignAdmissibilityExact are reused as structural donors. The finite collision is DASHI-owned and creates no empirical population, bias or harm claim."
