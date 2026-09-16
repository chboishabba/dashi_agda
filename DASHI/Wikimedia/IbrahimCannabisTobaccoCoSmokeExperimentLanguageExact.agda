module DASHI.Wikimedia.IbrahimCannabisTobaccoCoSmokeExperimentLanguageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimPesticideExperimentDesignParetoExact as Design
import DASHI.Wikimedia.IbrahimPesticideExperimentConsumerIndexedParetoExact as Indexed

------------------------------------------------------------------------
-- SAME-CONSUMER CANDIDATE LANGUAGE: MIXED CANNABIS + TOBACCO COMBUSTION
--
-- All candidates below answer the SAME declared consumer:
--   does mixed cannabis+tobacco combustion exhibit non-additive transfer or
--   thermal-product behaviour relative to the two source materials burned
--   separately?
--
-- This is the proper surface for Pareto comparison.  Designs that answer a
-- different consumer do not enter this language.
------------------------------------------------------------------------

data CoSmokeDesign : Set where
  sourceOnlyObservation
  fixedRatioThreeArm
  ratioResponseSeries
  deviceFactorialSeries : CoSmokeDesign

record CoSmokeCandidate : Set where
  constructor co-smoke-candidate
  field
    design : CoSmokeDesign
    declaredConsumer : Design.ScientificConsumer
    sourceIdentityBurden : Nat
    assayBurden : Nat
    executionBurden : Nat
    replicateBurden : Nat
    mixedInteractionInformation : Nat
    ratioResponseInformation : Nat
    deviceInteractionInformation : Nat
    hasMixedArm : Bool
    hasPureSourceArms : Bool
    sameSourceMaterialAcrossArms : Bool
    admissibleForNonAdditivityConsumer : Bool
    rationale : String
open CoSmokeCandidate public

sourceOnly : CoSmokeCandidate
sourceOnly = co-smoke-candidate
  sourceOnlyObservation
  Design.mixedCombustionInteractionConsumer
  1 1 1 1
  0 0 0
  false false true false
  "source residue vectors alone cannot distinguish additive from non-additive mixed combustion"

threeArm : CoSmokeCandidate
threeArm = co-smoke-candidate
  fixedRatioThreeArm
  Design.mixedCombustionInteractionConsumer
  2 3 3 3
  5 0 0
  true true true true
  "minimum direct design: cannabis-only, tobacco-only and one fixed-ratio mixed arm under matched combustion conditions"

ratioSeries : CoSmokeCandidate
ratioSeries = co-smoke-candidate
  ratioResponseSeries
  Design.mixedCombustionInteractionConsumer
  2 3 4 5
  5 5 0
  true true true true
  "adds multiple cannabis:tobacco ratios to estimate whether the mixed residual is dose-ratio dependent"

deviceFactorial : CoSmokeCandidate
deviceFactorial = co-smoke-candidate
  deviceFactorialSeries
  Design.mixedCombustionInteractionConsumer
  3 4 5 6
  5 4 5
  true true true true
  "crosses mixture arms with paper/filter/device conditions to estimate whether non-additivity is device dependent"

------------------------------------------------------------------------
-- Adequacy gate: source-only observation is excluded BEFORE Pareto ranking.
------------------------------------------------------------------------

data SourceOnlyAnswersMixedInteraction : Set where

sourceOnlyDoesNotAnswerMixedInteraction : SourceOnlyAnswersMixedInteraction → ⊥
sourceOnlyDoesNotAnswerMixedInteraction ()

record AdequacyGate : Set where
  constructor adequacy-gate
  field
    candidate : CoSmokeCandidate
    sameConsumerPaid : Bool
    mixedArmPaid : Bool
    pureSourceControlsPaid : Bool
    sameObjectIdentityPaid : Bool
    eligibleForPareto : Bool
open AdequacyGate public

sourceOnlyGate : AdequacyGate
sourceOnlyGate = adequacy-gate sourceOnly true false false true false

threeArmGate : AdequacyGate
threeArmGate = adequacy-gate threeArm true true true true true

ratioSeriesGate : AdequacyGate
ratioSeriesGate = adequacy-gate ratioSeries true true true true true

deviceFactorialGate : AdequacyGate
deviceFactorialGate = adequacy-gate deviceFactorial true true true true true

------------------------------------------------------------------------
-- Within-consumer Pareto structure.
--
-- The fixed-ratio design is the least-burden adequate discriminator for the
-- basic non-additivity query.  Richer designs pay extra coordinates, so they
-- are not discarded merely because the three-arm design is cheaper.
------------------------------------------------------------------------

record CoSmokeParetoReading : Set where
  constructor co-smoke-pareto-reading
  field
    cheapestAdequateBasicDiscriminator : CoSmokeDesign
    richerRatioCandidateRetained : Bool
    richerDeviceCandidateRetained : Bool
    sourceOnlyExcludedBeforeRanking : Bool
    threeArmGloballyDominatesRatioSeries : Bool
    threeArmGloballyDominatesDeviceFactorial : Bool
    reason : String
open CoSmokeParetoReading public

canonicalCoSmokeParetoReading : CoSmokeParetoReading
canonicalCoSmokeParetoReading = co-smoke-pareto-reading
  fixedRatioThreeArm
  true true true
  false false
  "three-arm is cheapest for the basic interaction consumer, while ratio and device series pay additional declared information coordinates"

------------------------------------------------------------------------
-- Adaptive escalation from the existing DASHI experiment-design rule.
------------------------------------------------------------------------

data CoSmokeEscalationTrigger : Set where
  basicInteractionResolved
  ratioDependenceUnresolved
  deviceDependenceUnresolved
  replicateUncertaintyTooLarge : CoSmokeEscalationTrigger

nextDesign : CoSmokeEscalationTrigger → CoSmokeDesign
nextDesign basicInteractionResolved = fixedRatioThreeArm
nextDesign ratioDependenceUnresolved = ratioResponseSeries
nextDesign deviceDependenceUnresolved = deviceFactorialSeries
nextDesign replicateUncertaintyTooLarge = fixedRatioThreeArm

record CoSmokeEscalationBoundary : Set where
  constructor co-smoke-escalation-boundary
  field
    startWithCheapestAdequateDesign : Bool
    ratioSeriesRequiresRatioConsumerResidual : Bool
    deviceFactorialRequiresDeviceResidual : Bool
    richerDesignAutomaticallyPreferred : Bool
    basicThreeArmCreatesDeploymentAuthority : Bool
open CoSmokeEscalationBoundary public

canonicalCoSmokeEscalationBoundary : CoSmokeEscalationBoundary
canonicalCoSmokeEscalationBoundary =
  co-smoke-escalation-boundary true true true false false

consumerIndexRetained : Bool
consumerIndexRetained =
  Indexed.sameConsumerRequiredForScientificDominance
    Indexed.canonicalConsumerIndexedParetoBoundary
