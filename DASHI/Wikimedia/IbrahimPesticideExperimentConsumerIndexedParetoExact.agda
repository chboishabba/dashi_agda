module DASHI.Wikimedia.IbrahimPesticideExperimentConsumerIndexedParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimPesticideExperimentDesignParetoExact as Design
import DASHI.Wikimedia.IbrahimPesticideExperimentDesignBoundedParetoExact as Native

------------------------------------------------------------------------
-- CONSUMER-INDEXED PARETO REPAIR
--
-- The native bounded-Pareto adapter deliberately exposed a WrongType risk:
-- experiments for different scientific consumers can appear to dominate one
-- another when projected onto generic burden/information axes.  Scientific
-- Pareto comparison is therefore indexed by the declared consumer.
--
-- Cross-consumer roadmap ordering is a separate preference / allocation layer.
------------------------------------------------------------------------

record ConsumerExperiment : Set where
  constructor consumer-experiment
  field
    consumer : Design.ScientificConsumer
    experiment : Design.ExperimentCarrier
    profile : Design.ExperimentParetoProfile
open ConsumerExperiment public

coSmokeConsumerExperiment : ConsumerExperiment
coSmokeConsumerExperiment = consumer-experiment
  Design.mixedCombustionInteractionConsumer
  Design.threeArmCoSmokeExperiment
  Design.coSmokeProfile

btConsumerExperiment : ConsumerExperiment
btConsumerExperiment = consumer-experiment
  Design.btHarvestBurdenConsumer
  Design.btHarvestSeriesExperiment
  Design.btProfile

glyphosateConsumerExperiment : ConsumerExperiment
glyphosateConsumerExperiment = consumer-experiment
  Design.glyphosateOccurrenceConsumer
  Design.glyphosateSurveyExperiment
  Design.glyphosateProfile

priorConsumerExperiment : ConsumerExperiment
priorConsumerExperiment = consumer-experiment
  Design.regulatoryModelFreshnessConsumer
  Design.exposurePriorBacktestExperiment
  Design.priorProfile

lifecycleConsumerExperiment : ConsumerExperiment
lifecycleConsumerExperiment = consumer-experiment
  Design.nonFoodToFoodLifecycleConsumer
  Design.lifecycleResidueExperiment
  Design.lifecycleProfile

------------------------------------------------------------------------
-- Comparability requires the same declared scientific consumer.
------------------------------------------------------------------------

record ConsumerComparable (a b : ConsumerExperiment) : Set where
  constructor consumer-comparable
  field
    sameConsumer : consumer a ≡ consumer b
open ConsumerComparable public

coSmokeSelfComparable : ConsumerComparable coSmokeConsumerExperiment coSmokeConsumerExperiment
coSmokeSelfComparable = consumer-comparable refl

btSelfComparable : ConsumerComparable btConsumerExperiment btConsumerExperiment
btSelfComparable = consumer-comparable refl

glyphosateSelfComparable : ConsumerComparable glyphosateConsumerExperiment glyphosateConsumerExperiment
glyphosateSelfComparable = consumer-comparable refl

------------------------------------------------------------------------
-- Cross-consumer comparison is blocked, even if generic numeric axes would
-- permit a Pareto.Dominates witness after erasing consumer identity.
------------------------------------------------------------------------

data CrossConsumerScientificDominance : Set where

data NarrativePriorityCreatesScientificDominance : Set where

data GenericInformationAxisCreatesConsumerAdequacy : Set where

crossConsumerDominanceForbidden : CrossConsumerScientificDominance → ⊥
crossConsumerDominanceForbidden ()

narrativePriorityDoesNotCreateScientificDominance : NarrativePriorityCreatesScientificDominance → ⊥
narrativePriorityDoesNotCreateScientificDominance ()

genericInformationAxisDoesNotCreateConsumerAdequacy : GenericInformationAxisCreatesConsumerAdequacy → ⊥
genericInformationAxisDoesNotCreateConsumerAdequacy ()

record CrossConsumerCollision : Set where
  constructor cross-consumer-collision
  field
    leftName : String
    leftConsumer : String
    rightName : String
    rightConsumer : String
    erasedAxisComparisonCanRank : Bool
    scientificDominancePaid : Bool
    reason : String
open CrossConsumerCollision public

coSmokeBtFalseDominanceWitness : CrossConsumerCollision
coSmokeBtFalseDominanceWitness = cross-consumer-collision
  "same-material cannabis+tobacco mixed-combustion experiment"
  "mixed-combustion interaction"
  "Bt post-application harvest burden series"
  "Bt harvest burden"
  true false
  "co-smoke may be cheaper and higher on generic route-information axes, but it does not answer the Bt-harvest consumer"

coSmokeGlyphosateFalseDominanceWitness : CrossConsumerCollision
coSmokeGlyphosateFalseDominanceWitness = cross-consumer-collision
  "same-material cannabis+tobacco mixed-combustion experiment"
  "mixed-combustion interaction"
  "glyphosate+AMPA cannabis survey"
  "glyphosate occurrence"
  true false
  "generic Pareto coordinates erase the analyte-observability consumer distinction"

------------------------------------------------------------------------
-- A cross-consumer research roadmap is allowed only after declaring a separate
-- meta-consumer.  It is then preference/resource allocation, not a theorem that
-- one scientific experiment dominates another.
------------------------------------------------------------------------

data MetaConsumer : Set where
  unresolvedRiskReductionPerResearchBurden
  regulatoryBlindSpotClosure
  inhalationExposureClosure : MetaConsumer

record RoadmapPreference : Set where
  constructor roadmap-preference
  field
    metaConsumer : MetaConsumer
    preferredFirst : ConsumerExperiment
    preferenceBasis : String
    budgetOrBurdenBasis : String
    scientificDominanceClaimed : Bool
    authorityClaimed : Bool
open RoadmapPreference public

currentRoadmapPreference : RoadmapPreference
currentRoadmapPreference = roadmap-preference
  inhalationExposureClosure
  coSmokeConsumerExperiment
  "current route-specific evidence gap is mixed cannabis+tobacco smoke transfer; this is a research-priority preference, not cross-consumer Pareto dominance"
  "same-material three-arm design has lower longitudinal burden than Bt/lifecycle experiments and directly closes an inhalation interaction residual"
  false false

------------------------------------------------------------------------
-- Per-consumer candidate languages can later be enlarged with alternative
-- designs for the SAME query, at which point native Pareto dominance and
-- BoundedParetoCompletenessExact apply without WrongType cross-consumer mixing.
------------------------------------------------------------------------

record ConsumerIndexedCandidateLanguage : Set where
  constructor consumer-indexed-candidate-language
  field
    declaredConsumer : Design.ScientificConsumer
    currentCandidate : ConsumerExperiment
    alternativeDesignsAcquired : Bool
    nativeParetoComparisonReady : Bool
    boundedCompletenessReady : Bool
open ConsumerIndexedCandidateLanguage public

coSmokeLanguage : ConsumerIndexedCandidateLanguage
coSmokeLanguage = consumer-indexed-candidate-language
  Design.mixedCombustionInteractionConsumer
  coSmokeConsumerExperiment
  false false false

btLanguage : ConsumerIndexedCandidateLanguage
btLanguage = consumer-indexed-candidate-language
  Design.btHarvestBurdenConsumer
  btConsumerExperiment
  false false false

glyphosateLanguage : ConsumerIndexedCandidateLanguage
glyphosateLanguage = consumer-indexed-candidate-language
  Design.glyphosateOccurrenceConsumer
  glyphosateConsumerExperiment
  false false false

priorLanguage : ConsumerIndexedCandidateLanguage
priorLanguage = consumer-indexed-candidate-language
  Design.regulatoryModelFreshnessConsumer
  priorConsumerExperiment
  false false false

lifecycleLanguage : ConsumerIndexedCandidateLanguage
lifecycleLanguage = consumer-indexed-candidate-language
  Design.nonFoodToFoodLifecycleConsumer
  lifecycleConsumerExperiment
  false false false

record ConsumerIndexedParetoBoundary : Set where
  constructor consumer-indexed-pareto-boundary
  field
    sameConsumerRequiredForScientificDominance : Bool
    crossConsumerRoadmapNeedsMetaConsumer : Bool
    roadmapPreferenceCreatesScientificDominance : Bool
    roadmapPreferenceCreatesAuthority : Bool
    nativeBoundedParetoReusablePerConsumer : Bool
    currentCrossConsumerFrontCertified : Bool
open ConsumerIndexedParetoBoundary public

canonicalConsumerIndexedParetoBoundary : ConsumerIndexedParetoBoundary
canonicalConsumerIndexedParetoBoundary =
  consumer-indexed-pareto-boundary true true false false true false

nativeAdapterRetained : Bool
nativeAdapterRetained =
  Native.allCandidatesMappedToNativeParetoCarrier
    Native.canonicalBoundedExperimentParetoStatus
