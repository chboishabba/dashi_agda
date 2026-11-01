module DASHI.Wikimedia.IbrahimPesticideExperimentDesignBoundedParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Environment.BoundedParetoCompletenessExact as Bounded
import DASHI.Environment.InversePlanning as Planning
import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Wikimedia.IbrahimPesticideExperimentDesignParetoExact as Design

------------------------------------------------------------------------
-- BOUNDED-PARETO ADAPTER FOR THE PESTICIDE EXPERIMENT LANGUAGE
--
-- The previous owner supplied five admissible experiment candidates and local
-- information/burden axes.  This module maps those candidates into the repo's
-- native ParetoPlanning carrier.  It deliberately does not fabricate
-- non-dominance proofs: until the exact vector relations are certified, the
-- Pareto front remains an unpaid execution/certification coordinate.
------------------------------------------------------------------------

mkExperimentPlan : String → Nat → Nat → Nat → Nat → Planning.Plan
mkExperimentPlan name identity assay execution longitudinal =
  Planning.mkPlan
    name
    []
    []
    []
    Latent.pathA-screening
    identity
    assay
    execution
    longitudinal

mkObjective : String → Pareto.Direction → Nat → String → Pareto.ObjectiveScore
mkObjective id dir v evidence =
  Pareto.mkObjectiveScore id dir v "synthetic experiment-design axis" evidence

objectivesFor : Design.ExperimentParetoProfile → List Pareto.ObjectiveScore
objectivesFor p =
  mkObjective "source-identity-burden" Pareto.minimise (Design.sourceIdentityBurden p)
    "same-object/sample identity burden" ∷
  mkObjective "assay-modality-burden" Pareto.minimise (Design.assayModalityBurden p)
    "number/specialisation of required observer modalities" ∷
  mkObjective "execution-complexity" Pareto.minimise (Design.executionComplexity p)
    "local synthetic execution-complexity axis" ∷
  mkObjective "longitudinal-burden" Pareto.minimise (Design.longitudinalBurden p)
    "need for repeated longitudinal sampling" ∷
  mkObjective "unresolved-consumer-coordinates-paid" Pareto.maximise
    (Design.unresolvedConsumerCoordinatesPaid p)
    "number of currently unresolved declared-consumer coordinates paid" ∷
  mkObjective "route-specific-information-gain" Pareto.maximise
    (Design.routeSpecificInformationGain p)
    "route-specific information gain for current contaminant consumer" ∷
  []

planFor : String → Design.ExperimentParetoProfile → Pareto.EvaluatedPlan
planFor name p =
  Pareto.mkEvaluatedPlan
    (mkExperimentPlan name
      (Design.sourceIdentityBurden p)
      (Design.assayModalityBurden p)
      (Design.executionComplexity p)
      (Design.longitudinalBurden p))
    true
    (objectivesFor p)
    ("DASHI synthetic experiment-design axes; not dollars, truth or authority" ∷
     "consumer adequacy/admissibility paid in IbrahimPesticideExperimentDesignParetoExact" ∷ [])

coSmokeEvaluated : Pareto.EvaluatedPlan
coSmokeEvaluated = planFor "same-material cannabis+tobacco three-arm combustion" Design.coSmokeProfile

btEvaluated : Pareto.EvaluatedPlan
btEvaluated = planFor "Bt post-application harvest burden series" Design.btProfile

glyphosateEvaluated : Pareto.EvaluatedPlan
glyphosateEvaluated = planFor "glyphosate+AMPA dedicated cannabis survey" Design.glyphosateProfile

priorBacktestEvaluated : Pareto.EvaluatedPlan
priorBacktestEvaluated = planFor "historical-vs-contemporary exposure-prior backtest" Design.priorProfile

lifecycleEvaluated : Pareto.EvaluatedPlan
lifecycleEvaluated = planFor "non-food to later food-bearing lifecycle residue study" Design.lifecycleProfile

declaredExperimentPopulation : List Pareto.EvaluatedPlan
declaredExperimentPopulation =
  coSmokeEvaluated ∷
  btEvaluated ∷
  glyphosateEvaluated ∷
  priorBacktestEvaluated ∷
  lifecycleEvaluated ∷
  []

------------------------------------------------------------------------
-- Native finite Pareto result shell.
--
-- The candidate language is now literal, but non-dominated candidates remain
-- empty until exact vector comparison receipts are proved.  This prevents a
-- prose priority from being mistaken for a certified Pareto front.
------------------------------------------------------------------------

currentFiniteParetoResult : Pareto.FiniteParetoResult
currentFiniteParetoResult =
  Pareto.mkFiniteParetoResult
    declaredExperimentPopulation
    []
    5
    "five experiment families declared by IbrahimPesticideExperimentDesignParetoExact; enlargement requires a new admissible experiment family or reopened observer collision"
    ("co-smoke has highest current narrative priority but no certified non-dominance receipt yet" ∷
     "Bt harvest and glyphosate/AMPA close different observer classes and may remain non-dominated tradeoffs" ∷
     "prior backtest is cheaper but pays a different regulatory consumer" ∷
     "lifecycle follow-up is high burden but uniquely answers non-food-to-food persistence" ∷ [])
    true

------------------------------------------------------------------------
-- Certification boundary to the existing bounded-completeness theorem.
------------------------------------------------------------------------

record BoundedExperimentParetoStatus : Set where
  constructor bounded-experiment-pareto-status
  field
    finiteCandidateLanguageWritten : Bool
    allCandidatesMappedToNativeParetoCarrier : Bool
    objectiveUnitsDeclaredSynthetic : Bool
    exactPairwiseDominanceReceiptsPaid : Bool
    nonDominatedFrontCertified : Bool
    boundedEnumerationCompletenessReceiptPaid : Bool
    globalContinuousOptimalityClaimed : Bool
    preferenceOrAuthoritySelected : Bool
    boundedCompletenessTheoremAvailable : Bool
open BoundedExperimentParetoStatus public

canonicalBoundedExperimentParetoStatus : BoundedExperimentParetoStatus
canonicalBoundedExperimentParetoStatus =
  bounded-experiment-pareto-status
    true true true
    false false false
    false false true

------------------------------------------------------------------------
-- The imported theorem pays the implication once two separate receipts exist:
--   1. complete bounded enumeration of the declared admissible language;
--   2. NonDominatedIn for a candidate.
-- We retain those premises explicitly rather than asserting them here.
------------------------------------------------------------------------

record NativeBoundedCompletenessBridge : Set where
  constructor native-bounded-completeness-bridge
  field
    theoremOwner : String
    requiredEnumerationReceipt : String
    requiredNonDominanceReceipt : String
    conclusionScope : String
    doesNotChoosePreference : Bool
open NativeBoundedCompletenessBridge public

canonicalNativeBoundedCompletenessBridge : NativeBoundedCompletenessBridge
canonicalNativeBoundedCompletenessBridge =
  native-bounded-completeness-bridge
    "DASHI.Environment.BoundedParetoCompletenessExact.completeEnumerationLiftsNonDominance"
    "Core.BoundedEnumeration over the declared pesticide experiment language"
    "Pareto.NonDominatedIn candidate declaredExperimentPopulation"
    "no admissible dominator in the declared finite experiment language only"
    true

boundedParetoOwnerImported : Bool
boundedParetoOwnerImported =
  Bounded.boundedCompletenessIsRelativeToDeclaredLanguage
    Bounded.canonicalBoundedParetoBoundary
