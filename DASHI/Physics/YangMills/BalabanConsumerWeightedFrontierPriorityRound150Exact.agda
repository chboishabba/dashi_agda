{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanConsumerWeightedFrontierPriorityRound150Exact where

------------------------------------------------------------------------
-- ROUND150: CONSUMER-WEIGHTED FRONTIER PRIORITY, NOT LEMMA COUNT
--
-- This is a search-planning heuristic over the exact BIDI dependency graph.  It
-- is not a mathematical importance theorem about Bałaban's sources.  The score
-- counts declared downstream consumers which a source identity directly feeds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.YangMills.BalabanPhysicalFrontierSearchHypergraphRound146Exact as R146
import DASHI.Physics.YangMills.BalabanFrontierExperimentDesignRound148Exact as R148

-- Consumers are theorem/programme surfaces, not paper sections.
data FrontierConsumer : Set where
  a1PresentCutConsumer
  a2PresentCutConsumer
  bc1EffectiveActionConsumer
  bc2HeatDoobConsumer
  sectorStressConsumer
  qftgrStressConsumer
  : FrontierConsumer

leafConsumers : R146.BalabanFrontierLeaf → List FrontierConsumer
leafConsumers R146.densityToCombinedRGState =
  bc1EffectiveActionConsumer ∷ bc2HeatDoobConsumer ∷ sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.combinedRGStateToBC1Potential =
  bc1EffectiveActionConsumer ∷ bc2HeatDoobConsumer ∷ sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.componentLocalizedD1ToPhysicalD1 =
  bc1EffectiveActionConsumer ∷ sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.stressInsertionEqualsPhysicalD1Sum =
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.metricPerturbationAdmission =
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.a1CouplingToBetaHistory =
  a1PresentCutConsumer ∷ sectorStressConsumer ∷ []
leafConsumers R146.a2CouplingToBetaHistory =
  a2PresentCutConsumer ∷ sectorStressConsumer ∷ []
leafConsumers R146.cmp119FiniteMeasureSchwingerEndpoint =
  sectorStressConsumer ∷ qftgrStressConsumer ∷ []
leafConsumers R146.unifiedSectorStressRecovery = qftgrStressConsumer ∷ []

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

alphaScore : R146.BalabanFrontierLeaf → Nat
alphaScore leaf = listLength (leafConsumers leaf)

-- The two semantic realization leaves are currently tied for the largest
-- declared fan-out in this planning model.  These equations are definitional
-- audit facts about the mapping above, not source theorems.
densityStateAlphaIsFour :
  alphaScore R146.densityToCombinedRGState ≡ suc (suc (suc (suc zero)))
densityStateAlphaIsFour = refl

statePotentialAlphaIsFour :
  alphaScore R146.combinedRGStateToBC1Potential ≡ suc (suc (suc (suc zero)))
statePotentialAlphaIsFour = refl

componentD1AlphaIsThree :
  alphaScore R146.componentLocalizedD1ToPhysicalD1 ≡ suc (suc (suc zero))
componentD1AlphaIsThree = refl

-- A priority receipt still requires least-privilege route admission.  Fan-out
-- cannot authorize a carrier mismatch or silent hypothesis strengthening.
record ConsumerWeightedPriority : Set₁ where
  field
    leaf : R146.BalabanFrontierLeaf
    route : R146.BalabanFrontierRoute
    routeTargetsLeaf : R146.routeSource route ≡ leaf
    admission : Least.RouteAdmission
    experimentCoordinate : R148.BalabanFrontierCoordinate
    experimentTargetsLeaf : R148.coordinateTargetsLeaf experimentCoordinate ≡ leaf

open ConsumerWeightedPriority public

priorityLiveSearch : ConsumerWeightedPriority → Least.LiveProofSearch
priorityLiveSearch receipt = Least.elaborateRoute (admission receipt)

-- Search policy boundary: alpha score is dependency fan-out only.  It neither
-- proves the leaf nor says the cheapest experiment is scientifically best.
record ConsumerWeightedPriorityBoundary : Set where
  constructor consumerWeightedPriorityBoundary
  field
    highestFanoutAutomaticallyProvesLeaf : Agda.Builtin.Bool.Bool
    highestFanoutAutomaticallyProvesLeafIsFalse :
      highestFanoutAutomaticallyProvesLeaf ≡ Agda.Builtin.Bool.false
    mostExperimentsAutomaticallyMeansMostProgress : Agda.Builtin.Bool.Bool
    mostExperimentsAutomaticallyMeansMostProgressIsFalse :
      mostExperimentsAutomaticallyMeansMostProgress ≡ Agda.Builtin.Bool.false

canonicalConsumerWeightedPriorityBoundary : ConsumerWeightedPriorityBoundary
canonicalConsumerWeightedPriorityBoundary =
  consumerWeightedPriorityBoundary Agda.Builtin.Bool.false refl Agda.Builtin.Bool.false refl

balabanConsumerWeightedFrontierPriorityLevel : ProofLevel
balabanConsumerWeightedFrontierPriorityLevel = machineChecked
