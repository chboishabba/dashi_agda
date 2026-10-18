module DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityParetoExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityReceipt as Ident

------------------------------------------------------------------------
-- ELIGIBLE-ONLY 3/6/9 PARETO ADAPTER
--
-- The runtime may measure multiple cost axes for N=3,6,9, but a model enters
-- Pareto comparison only after separate admissibility and consumer-adequacy
-- evidence is supplied.  Neither oscillator count nor description length is a
-- truth-maker.  This is a thin adapter over the repo-native
-- AdmissibleConsumerMDLHyperfabricExact owner.
------------------------------------------------------------------------

data OscillatorModel : Set where
  model3 model6 model9 : OscillatorModel

modelDescriptionLength : OscillatorModel → Nat
modelDescriptionLength model3 = 3
modelDescriptionLength model6 = 6
modelDescriptionLength model9 = 9

modelReference : OscillatorModel → String
modelReference model3 = "continuous oscillator model N=3"
modelReference model6 = "continuous oscillator model N=6"
modelReference model9 = "continuous oscillator model N=9"

data OscillatorParetoAxis : Set where
  modelSizeAxis : OscillatorParetoAxis
  heldoutErrorAxis : OscillatorParetoAxis
  hiddenStateErrorAxis : OscillatorParetoAxis
  restartInstabilityAxis : OscillatorParetoAxis
  nullFragilityAxis : OscillatorParetoAxis

axisReference : OscillatorParetoAxis → String
axisReference modelSizeAxis = "oscillator/model-size cost"
axisReference heldoutErrorAxis = "held-out reconstruction error cost"
axisReference hiddenStateErrorAxis = "canonical hidden-state recovery error cost"
axisReference restartInstabilityAxis = "restart/basin instability cost"
axisReference nullFragilityAxis = "noise/separation/transfer fragility cost"

record OscillatorParetoEvidence : Set₁ where
  constructor oscillator-pareto-evidence
  field
    AdmissibleEvidence : OscillatorModel → Set
    ConsumerAdequacyEvidence : OscillatorModel → Set
    measuredCost : OscillatorParetoAxis → OscillatorModel → Nat
    evidenceReference : String
    frozenBeforeHeldout : Bool
    heldoutDidNotTuneEligibilityRule : Bool
    numericalEvidenceCreatesTruth : Bool
open OscillatorParetoEvidence public

oscillatorConsumerMDLProblem :
  OscillatorParetoEvidence → MDL.ConsumerMDLProblem
oscillatorConsumerMDLProblem evidence = MDL.consumerMDLProblem
  OscillatorModel
  (AdmissibleEvidence evidence)
  (ConsumerAdequacyEvidence evidence)
  modelDescriptionLength
  _≡_
  modelReference
  "description-length coordinate is oscillator count only; runtime cost hyperfabric carries the remaining measured axes"
  "joint consumer: held-out waveform reconstruction plus declared query-indexed hidden-state adequacy"

oscillatorCostHyperfabric :
  (evidence : OscillatorParetoEvidence) →
  MDL.CostHyperfabric (oscillatorConsumerMDLProblem evidence)
oscillatorCostHyperfabric evidence = MDL.costHyperfabric
  OscillatorParetoAxis
  (measuredCost evidence)
  axisReference

modelEligible :
  (evidence : OscillatorParetoEvidence) →
  (model : OscillatorModel) → Set
modelEligible evidence model =
  MDL.Eligible (oscillatorConsumerMDLProblem evidence) model

modelParetoAdmissible :
  (evidence : OscillatorParetoEvidence) →
  (model : OscillatorModel) → Set₁
modelParetoAdmissible evidence model =
  MDL.ParetoAdmissible (oscillatorCostHyperfabric evidence) model

------------------------------------------------------------------------
-- The identifiability parent remains the semantic consumer source.  This
-- adapter does not replace its query-indexed adequacy test with a scalar score.
------------------------------------------------------------------------

identifiabilityParentQuery : Ident.OscillatorIdentifiabilityQuery
identifiabilityParentQuery = Ident.hiddenStateQuery

record OscillatorParetoCrossPollinationReceipt : Set where
  constructor oscillator-pareto-cross-pollination-receipt
  field
    queryIndexedIdentifiabilityParentRetained : Bool
    admissibleConsumerMDLParentRetained : Bool
    rankingOccursOnlyInsideEligibleStratum : Bool
    nullFragilityRemainsSeparateAxis : Bool
    heldoutErrorRemainsSeparateAxis : Bool
    noNewExternalScientificAuthorityCreated : Bool
open OscillatorParetoCrossPollinationReceipt public

canonicalOscillatorParetoCrossPollinationReceipt :
  OscillatorParetoCrossPollinationReceipt
canonicalOscillatorParetoCrossPollinationReceipt =
  oscillator-pareto-cross-pollination-receipt
    true true true true true true

------------------------------------------------------------------------
-- WrongType / promotion boundary.
------------------------------------------------------------------------

record OscillatorIdentifiabilityParetoBoundary : Set where
  constructor oscillator-identifiability-pareto-boundary
  field
    model3WinsByDefinition : Bool
    model6WinsByDefinition : Bool
    model9WinsByDefinition : Bool
    lowerDescriptionLengthCreatesTruth : Bool
    lowerHeldoutErrorCreatesMechanismIdentity : Bool
    paretoFrontierCreatesEmpiricalAuthority : Bool
    ineligibleModelMayWinByCheapness : Bool
    queryInadequateModelMayWinByCheapness : Bool
    measuredNullFragilityCreatesExactNonidentifiability : Bool
    eligibleOnlyRankingRetained : Bool
open OscillatorIdentifiabilityParetoBoundary public

canonicalOscillatorIdentifiabilityParetoBoundary :
  OscillatorIdentifiabilityParetoBoundary
canonicalOscillatorIdentifiabilityParetoBoundary =
  oscillator-identifiability-pareto-boundary
    false false false false false false false false false true
