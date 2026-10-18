module DASHI.Law.SensibLawDashiTradeTypedExplanationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawTypedAnswerChangingExplanationExact as Explain
import DASHI.Law.SensibLawDashiTradeComparativeAdapterExact as Trade

------------------------------------------------------------------------
-- M11 DASHITRADE PHASE-9 -> SHARED TYPED EXPLANATION ABI
--
-- A Phase-9 regime/posture/gate/cost chain may justify why action
-- applicability changed. It does not prove the realised market path, nor turn
-- a profitable trajectory into a globally true market theory.
------------------------------------------------------------------------

phase9AnswerChangeStep : Explain.AnswerChangeStep
phase9AnswerChangeStep =
  Explain.answer-change-step
    "delta:dashitrade:phase9-applicability"
    Locus.applicabilityLayer
    "coordinate:dashitrade:phase9-gate"
    "route:dashitrade:phase9-action"
    "Phase-9 regime/posture/gate/cost chain changes action applicability; realised market outcome remains separately observed"
    true refl
    false refl

phase9LayerIsApplicability :
  Explain.layer phase9AnswerChangeStep ≡ Locus.applicabilityLayer
phase9LayerIsApplicability = refl

record Phase9JustificationRefs : Set where
  constructor phase9-justification-refs
  field
    regimeRefPresent : Bool
    regimeRefPresentIsTrue : regimeRefPresent ≡ true
    postureRefPresent : Bool
    postureRefPresentIsTrue : postureRefPresent ≡ true
    actuatorRefPresent : Bool
    actuatorRefPresentIsTrue : actuatorRefPresent ≡ true
    costModelRefPresent : Bool
    costModelRefPresentIsTrue : costModelRefPresent ≡ true
    expectedSurplusRefPresent : Bool
    expectedSurplusRefPresentIsTrue : expectedSurplusRefPresent ≡ true
    realisedSurplusRefPresent : Bool
    realisedSurplusRefPresentIsTrue : realisedSurplusRefPresent ≡ true

canonicalPhase9JustificationRefs : Phase9JustificationRefs
canonicalPhase9JustificationRefs =
  phase9-justification-refs
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

tradeBoundary : Trade.DashiTradeComparativeBoundary
tradeBoundary = Trade.canonicalDashiTradeComparativeBoundary

justificationStillDoesNotCreateCausalProof :
  Trade.justificationChainCreatesCausalProof tradeBoundary ≡ false
justificationStillDoesNotCreateCausalProof = refl

realisedProfitStillDoesNotCreateGlobalTheoryTruth :
  Trade.realisedProfitCreatesGlobalTheoryTruth tradeBoundary ≡ false
realisedProfitStillDoesNotCreateGlobalTheoryTruth = refl

data Phase9ExplanationPredictsMarketOutcome : Set where
data Phase9ExplanationCreatesClaimTruth : Set where
data MissingPhase9JustificationMayBeInferred : Set where

phase9ExplanationDoesNotPredictMarketOutcome :
  Phase9ExplanationPredictsMarketOutcome → ⊥
phase9ExplanationDoesNotPredictMarketOutcome ()

phase9ExplanationDoesNotCreateTruth :
  Phase9ExplanationCreatesClaimTruth → ⊥
phase9ExplanationDoesNotCreateTruth ()

missingPhase9JustificationRemainsUnresolved :
  MissingPhase9JustificationMayBeInferred → ⊥
missingPhase9JustificationRemainsUnresolved ()

record DashiTradeTypedExplanationBoundary : Set where
  constructor dashiTradeTypedExplanationBoundary
  field
    usesSharedTypedExplanationAbi : Bool
    usesSharedTypedExplanationAbiIsTrue :
      usesSharedTypedExplanationAbi ≡ true

    phase9ChangeTypedApplicability : Bool
    phase9ChangeTypedApplicabilityIsTrue :
      phase9ChangeTypedApplicability ≡ true

    justificationRefsRetained : Bool
    justificationRefsRetainedIsTrue :
      justificationRefsRetained ≡ true

    explanationPredictsMarketOutcome : Bool
    explanationPredictsMarketOutcomeIsFalse :
      explanationPredictsMarketOutcome ≡ false

    explanationCreatesClaimTruth : Bool
    explanationCreatesClaimTruthIsFalse :
      explanationCreatesClaimTruth ≡ false

open DashiTradeTypedExplanationBoundary public

canonicalDashiTradeTypedExplanationBoundary :
  DashiTradeTypedExplanationBoundary
canonicalDashiTradeTypedExplanationBoundary =
  dashiTradeTypedExplanationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
