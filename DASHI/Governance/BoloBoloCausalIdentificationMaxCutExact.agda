module DASHI.Governance.BoloBoloCausalIdentificationMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification
import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment
import DASHI.Governance.OccupyCoordinationCausalPromotionExact as OccupyCausal

------------------------------------------------------------------------
-- BOLO'BOLO CAUSAL-IDENTIFICATION MAX-CUT
--
-- The governance lane already has a candidate DAG, process observables, a
-- paired flat-vs-nested experiment design and promotion obligations.  This
-- owner closes the remaining formal seam between those ingredients and the
-- repository's generic causal-estimand / identification-family machinery:
--
--   observed or paired outcomes
--     != causal estimand
--     != admissible identification receipt
--     != target causal effect
--     != political recommendation.
--
-- This is DASHI methodology.  It is not a claim by p.m., Occupy participants,
-- comparator authors, Ostrom, Baldwin or any other external source.
------------------------------------------------------------------------

record BoloCoordinationCausalEstimandDemand : Set where
  constructor bolo-coordination-causal-estimand-demand
  field
    estimandKind : Estimand.CausalEstimandKind
    populationReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    horizonReference : String
    causalQuestionReference : String

    candidateGraphAlreadyExists : Bool
    pairedExperimentDesignAlreadyExists : Bool
    observedOrDesignedContrastIdentifiesEffect : Bool

open BoloCoordinationCausalEstimandDemand public

canonicalBoloCoordinationCausalEstimandDemand :
  BoloCoordinationCausalEstimandDemand
canonicalBoloCoordinationCausalEstimandDemand =
  bolo-coordination-causal-estimand-demand
    Estimand.trajectoryEffect
    "predeclared target population / matched governance units"
    "nested kana-bolo-tega-like governance arm"
    "flat globally coupled consensus arm"
    "predeclared coordination outcome/cost trajectory including interface load, backlog and realised topology"
    "predeclared longitudinal follow-up horizon"
    "causal-question:bolo-flat-vs-nested:persistent-coordination-effect"
    true
    true
    false

------------------------------------------------------------------------
-- Identification-paid target bridge.
--
-- There is deliberately no canonical inhabitant.  A future empirical study
-- must supply one actual repository CausalEffectEstimand whose scope references
-- are the same target question, plus one obligation-admissible identification
-- family receipt.  Equal numbers or a favourable paired contrast cannot bypass
-- this same-object binding.
------------------------------------------------------------------------

record IdentifiedBoloCoordinationCausalBridge
    (demand : BoloCoordinationCausalEstimandDemand) : Set₂ where
  constructor identified-bolo-coordination-causal-bridge
  field
    estimand : Estimand.CausalEffectEstimand

    estimandKindMatches :
      Estimand.kind estimand ≡ BoloCoordinationCausalEstimandDemand.estimandKind demand
    populationMatches :
      Estimand.populationReference (Estimand.scope estimand)
      ≡ BoloCoordinationCausalEstimandDemand.populationReference demand
    interventionMatches :
      Estimand.interventionReference (Estimand.scope estimand)
      ≡ BoloCoordinationCausalEstimandDemand.interventionReference demand
    comparatorMatches :
      Estimand.comparatorReference (Estimand.scope estimand)
      ≡ BoloCoordinationCausalEstimandDemand.comparatorReference demand
    outcomeMatches :
      Estimand.outcomeReference (Estimand.scope estimand)
      ≡ BoloCoordinationCausalEstimandDemand.outcomeReference demand
    horizonMatches :
      Estimand.timeHorizonReference (Estimand.scope estimand)
      ≡ BoloCoordinationCausalEstimandDemand.horizonReference demand

    identificationFamily : Identification.CausalIdentificationFamily
    identificationGate :
      Identification.IdentificationEvidenceGate identificationFamily
    identificationQuestionMatches :
      Identification.causalQuestionAffordanceReference identificationGate
      ≡ BoloCoordinationCausalEstimandDemand.causalQuestionReference demand

    estimandAndIdentificationReviewedTogether : Bool
    estimandAndIdentificationReviewedTogetherIsTrue :
      estimandAndIdentificationReviewedTogether ≡ true

    directOutcomeContrastAloneProvidesIdentification : Bool
    directOutcomeContrastAloneProvidesIdentificationIsFalse :
      directOutcomeContrastAloneProvidesIdentification ≡ false

    comparatorEvidenceAloneProvidesIdentification : Bool
    comparatorEvidenceAloneProvidesIdentificationIsFalse :
      comparatorEvidenceAloneProvidesIdentification ≡ false

    createsPoliticalLegitimacy : Bool
    createsPoliticalLegitimacyIsFalse : createsPoliticalLegitimacy ≡ false

    bridgeReference : String

open IdentifiedBoloCoordinationCausalBridge public

------------------------------------------------------------------------
-- Existing generic non-collapse theorems, exposed on the governance surface.
------------------------------------------------------------------------

existingIdentificationDoesNotDetermineEstimand :
  Estimand.IdentificationMeansEstimandKnownPermission → ⊥
existingIdentificationDoesNotDetermineEstimand =
  Estimand.identificationDoesNotDetermineEstimand

existingLongitudinalOrderDoesNotIdentifyCause :
  Identification.LongitudinalMeansCausationPermission → ⊥
existingLongitudinalOrderDoesNotIdentifyCause =
  Identification.longitudinalOrderDoesNotByItselfIdentifyCause

existingIdentificationFamilyDoesNotProveEffect :
  Identification.IdentificationFamilyAutomaticallyProvesCausalEffectPermission → ⊥
existingIdentificationFamilyDoesNotProveEffect =
  Identification.identificationFamilyDoesNotAutomaticallyProveCausalEffect

------------------------------------------------------------------------
-- Application-specific firewalls.
------------------------------------------------------------------------

data CandidateDAGMeansIdentifiedEffectPermission : Set where
data PairedDesignMeansIdentifiedEffectPermission : Set where
data HistoricalComparatorMeansTargetEffectPermission : Set where
data SameScalarOutcomeMeansSameEstimandPermission : Set where
data IdentifiedCoordinationEffectMeansLegitimacyPermission : Set where

candidateDAGDoesNotIdentifyEffect :
  CandidateDAGMeansIdentifiedEffectPermission → ⊥
candidateDAGDoesNotIdentifyEffect ()

pairedDesignDoesNotIdentifyEffect :
  PairedDesignMeansIdentifiedEffectPermission → ⊥
pairedDesignDoesNotIdentifyEffect ()

historicalComparatorDoesNotIdentifyTargetEffect :
  HistoricalComparatorMeansTargetEffectPermission → ⊥
historicalComparatorDoesNotIdentifyTargetEffect ()

sameScalarDoesNotIdentifyEstimand :
  SameScalarOutcomeMeansSameEstimandPermission → ⊥
sameScalarDoesNotIdentifyEstimand ()

identifiedCoordinationEffectDoesNotCreateLegitimacy :
  IdentifiedCoordinationEffectMeansLegitimacyPermission → ⊥
identifiedCoordinationEffectDoesNotCreateLegitimacy ()

------------------------------------------------------------------------
-- Current status.
------------------------------------------------------------------------

record BoloCausalIdentificationBoundary : Set where
  constructor bolo-causal-identification-boundary
  field
    candidateCausalGraphPaid : Bool
    pairedExperimentDesignPaid : Bool
    explicitTargetEstimandRequired : Bool
    admissibleIdentificationGateRequired : Bool
    estimandScopeMustMatchTargetQuestion : Bool
    identificationQuestionMustMatchTargetQuestion : Bool

    pairedExperimentDesignAloneIdentifiesEffect : Bool
    historicalComparatorEvidenceAloneIdentifiesTargetEffect : Bool
    identificationDeterminesEstimand : Bool
    longitudinalOrderAloneIdentifiesCause : Bool
    targetCausalEffectIdentified : Bool
    identifiedEffectAutomaticallyCreatesLegitimacy : Bool

open BoloCausalIdentificationBoundary public

canonicalBoloCausalIdentificationBoundary : BoloCausalIdentificationBoundary
canonicalBoloCausalIdentificationBoundary =
  bolo-causal-identification-boundary
    true true true true true true
    false false false false false false

canonicalBoloCausalIdentificationReceipt : GenericReceipt.GenericReceipt
canonicalBoloCausalIdentificationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo target causal-estimand and identification-family max-cut"
    "DASHI.Governance.BoloBoloCausalIdentificationMaxCutExact"
    "canonicalBoloCoordinationCausalEstimandDemand / IdentifiedBoloCoordinationCausalBridge / canonicalBoloCausalIdentificationBoundary"
    "binds the flat-vs-nested persistent coordination question to the repository CausalEffectEstimand carrier and requires an obligation-admissible CausalIdentificationFamily gate whose question and estimand scope match the same target population, intervention, comparator, outcome and longitudinal horizon"
    "no identified target effect is manufactured: the existing candidate DAG, paired experiment design, historical comparators, equal scalar outcomes and longitudinal order do not themselves identify causation, and even an identified coordination effect would not create political legitimacy or total political superiority"
    "agda -i . DASHI/Governance/BoloBoloCausalIdentificationMaxCutRegression.agda"
