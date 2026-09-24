module DASHI.Culture.CohnInstitutionalEligibleMissingCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionSixExact as SourceSix
import DASHI.Governance.RelationalFlowGateAlgebra as Gate

------------------------------------------------------------------------
-- ELIGIBLE-BUT-MISSING REALISED-CARRIER NONFACTORABILITY
--
-- Extension six supplies three source-bounded missingness mechanisms:
-- non-disclosure, survey nonresponse and differential consent/opt-out.
-- This file supplies the finite DASHI theorem promised by that acquisition
-- owner. The sources motivate candidate observations; they do not populate a
-- real institution or own the theorem below.
------------------------------------------------------------------------

data EligiblePopulationState : Set where
  eligibleWithNonDisclosureMissing : EligiblePopulationState
  eligibleWithNonresponseMissing : EligiblePopulationState
  eligibleWithConsentMissing : EligiblePopulationState

data EligibilitySurface : Set where
  targetPopulationEligible : EligibilitySurface

data RealisedCarrier : Set where
  sameRealisedParticipantSurface : RealisedCarrier

data MissingPopulationProfile : Set where
  nonDisclosureMissingProfile : MissingPopulationProfile
  nonresponseMissingProfile : MissingPopulationProfile
  differentialConsentMissingProfile : MissingPopulationProfile

eligibilitySurface : EligiblePopulationState → EligibilitySurface
eligibilitySurface _ = targetPopulationEligible

realisedCarrier : EligiblePopulationState → RealisedCarrier
realisedCarrier _ = sameRealisedParticipantSurface

missingPopulationProfile : EligiblePopulationState → MissingPopulationProfile
missingPopulationProfile eligibleWithNonDisclosureMissing = nonDisclosureMissingProfile
missingPopulationProfile eligibleWithNonresponseMissing = nonresponseMissingProfile
missingPopulationProfile eligibleWithConsentMissing = differentialConsentMissingProfile

sameRealisedNonDisclosureNonresponse :
  realisedCarrier eligibleWithNonDisclosureMissing
  ≡ realisedCarrier eligibleWithNonresponseMissing
sameRealisedNonDisclosureNonresponse = refl

sameRealisedNonresponseConsent :
  realisedCarrier eligibleWithNonresponseMissing
  ≡ realisedCarrier eligibleWithConsentMissing
sameRealisedNonresponseConsent = refl

nonDisclosureNonresponseDiffer :
  missingPopulationProfile eligibleWithNonDisclosureMissing
  ≡ missingPopulationProfile eligibleWithNonresponseMissing → ⊥
nonDisclosureNonresponseDiffer ()

nonresponseConsentDiffer :
  missingPopulationProfile eligibleWithNonresponseMissing
  ≡ missingPopulationProfile eligibleWithConsentMissing → ⊥
nonresponseConsentDiffer ()

realisedCarrierMissingWitness :
  INF.NonFactorabilityWitness realisedCarrier missingPopulationProfile
realisedCarrierMissingWitness =
  INF.nonFactorabilityWitness
    eligibleWithNonDisclosureMissing
    eligibleWithNonresponseMissing
    sameRealisedNonDisclosureNonresponse
    nonDisclosureNonresponseDiffer

missingPopulationDoesNotFactorThroughRealisedCarrier :
  INF.FactorsThrough realisedCarrier missingPopulationProfile → ⊥
missingPopulationDoesNotFactorThroughRealisedCarrier =
  INF.witnessRulesOutEveryFlatFactorisation realisedCarrierMissingWitness

------------------------------------------------------------------------
-- Existing eligibility/gate separation is reused; no eligibility ontology is
-- created here.
------------------------------------------------------------------------

eligibilityAndRealisationRemainDistinct :
  {Eligible Assessment : Set} → Gate.DistinctCoordinates Eligible Assessment
eligibilityAndRealisationRemainDistinct = Gate.coordinatesKeptDistinct

------------------------------------------------------------------------
-- Source anchors: three mechanisms remain distinct source coordinates.
------------------------------------------------------------------------

nonDisclosureSource = SourceSix.grimesHiddenPopulation
nonresponseSource = SourceSix.standishUmbachNonresponse
consentSource = SourceSix.liLearningAnalyticsConsent

nonDisclosureTraversal = SourceSix.grimesToEligibleButMissing
nonresponseTraversal = SourceSix.standishToEligibleButMissing
consentTraversal = SourceSix.liToEligibleButMissing

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record EligibleMissingBoundary : Set where
  constructor eligible-missing-boundary
  field
    realisedCarrierDeterminesMissingPopulation : Bool
    nonDisclosureResponseConsentCollapsed : Bool
    sourceAcquisitionCreatesCarrierObservation : Bool
    eligiblePopulationEqualsRealisedCarrier : Bool
    missingPopulationIsConsumerRelevant : Bool
    sameRealisedSurfaceMayHideDifferentMissingPopulation : Bool
    sourceMechanismDefinitionallyEqualsDashiWorldState : Bool
    unverifiedQidMayRepairMissingObservation : Bool

open EligibleMissingBoundary public

canonicalEligibleMissingBoundary : EligibleMissingBoundary
canonicalEligibleMissingBoundary = eligible-missing-boundary
  false
  false
  false
  false
  true
  true
  false
  false

------------------------------------------------------------------------
-- Frontier consequence.
------------------------------------------------------------------------

record EligibleMissingFrontier : Set where
  constructor eligible-missing-frontier
  field
    p0Question : String
    finiteWitness : String
    sourceMechanisms : String
    theorem : String
    proofSearchImplication : String
    stopRule : String

open EligibleMissingFrontier public

canonicalEligibleMissingFrontier : EligibleMissingFrontier
canonicalEligibleMissingFrontier = eligible-missing-frontier
  "who belongs to the eligible/target population but is absent from the realised institutional or analytic carrier?"
  "same realised participant surface; distinct eligible-but-missing profile"
  "non-disclosure; survey nonresponse; differential consent/opt-out"
  "MissingPopulationProfile does not factor through RealisedCarrier"
  "a consumer that cares about eligible-but-missing people must probe the missingness mechanism rather than infer it from the realised carrier"
  "do not assign a source-specific missingness profile to a real institution without an observation; use proof-search/369 only to schedule the next discriminator"
