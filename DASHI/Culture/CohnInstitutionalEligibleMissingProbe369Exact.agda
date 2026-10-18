module DASHI.Culture.CohnInstitutionalEligibleMissingProbe369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.CohnInstitutionalEligibleMissingCarrierExact as Carrier
import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic
import DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact as Scheduler

------------------------------------------------------------------------
-- ELIGIBLE-BUT-MISSING PROOF-SEARCH / 369 RETURN
--
-- The carrier theorem says the realised participant surface cannot recover the
-- missing-population profile.  This owner turns that residual into an explicit
-- discriminator and consumer-relative next information move.  It reuses the
-- canonical proof-search and 369 scheduling grammars rather than adding a new
-- planner.
------------------------------------------------------------------------

data MissingnessProbe : Set where
  inspectDisclosureGate : MissingnessProbe
  inspectNonresponseGate : MissingnessProbe
  inspectConsentOptOutGate : MissingnessProbe

missingnessProbe : Carrier.EligiblePopulationState → MissingnessProbe
missingnessProbe Carrier.eligibleWithNonDisclosureMissing = inspectDisclosureGate
missingnessProbe Carrier.eligibleWithNonresponseMissing = inspectNonresponseGate
missingnessProbe Carrier.eligibleWithConsentMissing = inspectConsentOptOutGate

probeDiffersNonDisclosureNonresponse :
  missingnessProbe Carrier.eligibleWithNonDisclosureMissing
  ≡ missingnessProbe Carrier.eligibleWithNonresponseMissing → ⊥
probeDiffersNonDisclosureNonresponse ()

realisedCarrierCannotDetermineMissingnessProbe :
  INF.FactorsThrough Carrier.realisedCarrier missingnessProbe → ⊥
realisedCarrierCannotDetermineMissingnessProbe =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Carrier.eligibleWithNonDisclosureMissing
      Carrier.eligibleWithNonresponseMissing
      Carrier.sameRealisedNonDisclosureNonresponse
      probeDiffersNonDisclosureNonresponse)

------------------------------------------------------------------------
-- Canonical dialectical search role.
------------------------------------------------------------------------

missingPopulationSearchDiscriminator : Dialectic.SearchDiscriminator
missingPopulationSearchDiscriminator = Dialectic.searchDiscriminator
  "eligible-but-missing institutional population"
  "evidence that the realised carrier adequately covers the declared eligible population"
  "evidence of non-disclosure, nonresponse, consent/opt-out, or another declared missingness gate"
  "missing-population profile / visibility gate"
  "same realised carrier can coexist with different eligible-but-missing populations"

dialecticalSearchBoundary : Dialectic.DialecticalSearchBoundary
dialecticalSearchBoundary = Dialectic.canonicalDialecticalSearchBoundary

------------------------------------------------------------------------
-- 369 consumer-relative scheduling adapter.
------------------------------------------------------------------------

data CarrierConsumer : Set where
  realisedCarrierOnlyConsumer : CarrierConsumer
  eligiblePopulationCoverageConsumer : CarrierConsumer

coveragePlan : CarrierConsumer → Scheduler.ScheduledPlan
coveragePlan realisedCarrierOnlyConsumer = Scheduler.stopNow
coveragePlan eligiblePopulationCoverageConsumer = Scheduler.runSharedContext

addingCoverageConsumerChangesPlan :
  coveragePlan realisedCarrierOnlyConsumer
  ≡ coveragePlan eligiblePopulationCoverageConsumer → ⊥
addingCoverageConsumerChangesPlan ()

materialisedCarrierSurface : CarrierConsumer → Carrier.RealisedCarrier
materialisedCarrierSurface _ = Carrier.sameRealisedParticipantSurface

consumerRevisionPreservesCarrierSurface :
  materialisedCarrierSurface realisedCarrierOnlyConsumer
  ≡ materialisedCarrierSurface eligiblePopulationCoverageConsumer
consumerRevisionPreservesCarrierSurface = refl

schedulerBoundary : Scheduler.Spacy369AdaptiveConsumerProbeSchedulerBoundary
schedulerBoundary = Scheduler.canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record EligibleMissingProbeBoundary : Set where
  constructor eligible-missing-probe-boundary
  field
    realisedCarrierDeterminesMissingnessProbe : Bool
    canonicalDialecticalProofSearchReused : Bool
    canonical369SchedulerBoundaryReused : Bool
    consumerRevisionRewritesRealisedCarrier : Bool
    sourceCitationSelectsObservedMissingnessMechanism : Bool
    everyMissingnessMechanismIsDefinitionallySame : Bool
    probeResultAutomaticallyProvesInstitutionalBias : Bool

open EligibleMissingProbeBoundary public

canonicalEligibleMissingProbeBoundary : EligibleMissingProbeBoundary
canonicalEligibleMissingProbeBoundary = eligible-missing-probe-boundary
  false
  true
  true
  false
  false
  false
  false

------------------------------------------------------------------------
-- Frontier consequence.
------------------------------------------------------------------------

record EligibleMissingProbeFrontier : Set where
  constructor eligible-missing-probe-frontier
  field
    residual : String
    discriminator : String
    candidateProbes : String
    schedulerEffect : String
    frozenEvidenceRule : String
    nextMove : String

open EligibleMissingProbeFrontier public

canonicalEligibleMissingProbeFrontier : EligibleMissingProbeFrontier
canonicalEligibleMissingProbeFrontier = eligible-missing-probe-frontier
  "eligible population minus realised institutional/analytic carrier"
  "which visibility gate explains the missing population for the declared consumer?"
  "inspect disclosure; inspect nonresponse; inspect consent/opt-out"
  "realised-carrier-only consumer may stop; eligible-population coverage consumer opens an additional probe"
  "changing the consumer/probe policy does not rewrite the materialised realised carrier"
  "obtain a real observation for the relevant gate before assigning a source-specific missingness mechanism"
