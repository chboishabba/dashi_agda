module DASHI.Governance.KnowledgeCaptureSelectionFeedback20261101Exact where

------------------------------------------------------------------------
-- SELECTION / POSIWID / INCIDENT-SAFETY-REGULATION FEEDBACK
-- Owner: new synthetic DASHI finite countermodels.
-- Reuses original economic moat, epistemic option-cone, and source atlas
-- rather than importing unmerged circular-financing PR #1101.
--
-- Attribution: Stafford Beer, Brain of the Firm (1972; POSIWID phrase
-- associated with Beer); George J. Stigler, "The Theory of Economic
-- Regulation", Bell J Econ (1971), DOI 10.2307/3003160.
-- Mechanism and finite proofs below are distinct DASHI synthesis, not
-- theorem claims of those authors. Public stated aims and realised
-- selection functions are deliberately not identified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Economics.AISafetyRegulatoryMoatGameExact as Moat
import DASHI.Governance.KnowledgeProcessingSovereignCaptureExact as Knowledge
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Atlas

-- A claimed common risk rationale may coexist with sharply different
-- effective market structures, even without a motive or collusion witness.

data RegulatoryRoute : Set where
  proportionalReview exclusiveFixedCostGate : RegulatoryRoute

claimedHazardResponse : RegulatoryRoute → Bool
claimedHazardResponse proportionalReview = true
claimedHazardResponse exclusiveFixedCostGate = true

incumbentAbsorbsCost : RegulatoryRoute → Bool
incumbentAbsorbsCost proportionalReview = true
incumbentAbsorbsCost exclusiveFixedCostGate = true

openWeightPracticalAccess : RegulatoryRoute → Bool
openWeightPracticalAccess proportionalReview = true
openWeightPracticalAccess exclusiveFixedCostGate = false

incumbentStructuralBenefit : RegulatoryRoute → Bool
incumbentStructuralBenefit proportionalReview = false
incumbentStructuralBenefit exclusiveFixedCostGate = true

identicalPublicRationale :
  claimedHazardResponse proportionalReview
  ≡ claimedHazardResponse exclusiveFixedCostGate
identicalPublicRationale = refl

distinctIncumbentBenefit :
  incumbentStructuralBenefit proportionalReview
  ≡ incumbentStructuralBenefit exclusiveFixedCostGate → ⊥
distinctIncumbentBenefit ()

differentOpenWeightAccess :
  openWeightPracticalAccess proportionalReview
  ≡ openWeightPracticalAccess exclusiveFixedCostGate → ⊥
differentOpenWeightAccess ()

-- This is a non-identifiability witness: the same stated goal does not
-- allow an observer to recover actual downstream access and rents.

record SameRationaleDifferentMaterialOutcome : Set where
  constructor sameRationaleDifferentMaterialOutcome
  field
    sameClaim :
      claimedHazardResponse proportionalReview
      ≡ claimedHazardResponse exclusiveFixedCostGate
    differentAccess :
      openWeightPracticalAccess proportionalReview
      ≡ openWeightPracticalAccess exclusiveFixedCostGate → ⊥
    differentBenefit :
      incumbentStructuralBenefit proportionalReview
      ≡ incumbentStructuralBenefit exclusiveFixedCostGate → ⊥

publicRationaleCannotDetermineActualDistribution :
  SameRationaleDifferentMaterialOutcome
publicRationaleCannotDetermineActualDistribution =
  sameRationaleDifferentMaterialOutcome
    identicalPublicRationale differentOpenWeightAccess distinctIncumbentBenefit

-- Bounded endogenous feedback: selective reinforcement can perpetuate
-- a costly gate without any separate proof of manufactured incidents.
-- The transition is an explicitly stated toy mechanism, NOT an
-- empirical claim about Anthropic, government officials, or other actors.

data PolicyState : Set where
  pluralChoice concentratedChoice : PolicyState

select : PolicyState → RegulatoryRoute
select pluralChoice = proportionalReview
select concentratedChoice = exclusiveFixedCostGate

benefitFeedback : PolicyState → PolicyState
benefitFeedback pluralChoice = concentratedChoice
benefitFeedback concentratedChoice = concentratedChoice

benefitReinforced :
  benefitFeedback concentratedChoice ≡ concentratedChoice
benefitReinforced = refl

selectedConcentratedRegimeBenefitsIncumbent :
  incumbentStructuralBenefit (select (benefitFeedback pluralChoice))
  ≡ true
selectedConcentratedRegimeBenefitsIncumbent = refl

selectedConcentratedRegimeRestrictsOpenWeights :
  openWeightPracticalAccess (select (benefitFeedback pluralChoice))
  ≡ false
selectedConcentratedRegimeRestrictsOpenWeights = refl

-- The model captures effective selection in an asserted transition,
-- not observed actor preferences, feasibility, legality or causality.
-- A real policy requires same-object costs and regulator decision traces.

data NarrativeObject : Set where
  trueIncident incidentCoverage legalProposal operativeRule realisedEffect
    intentionalManipulation : NarrativeObject

record EmpiricalSelectionProducer : Set where
  constructor empiricalSelectionProducer
  field
    originalIncidentIdentifier : String
    originalProposalIdentifier : String
    exactEnactedRuleIdentifier : String
    measuredActorClassBurden : String
    observedEntrantResponse : String
    causalDesignOrCounterfactual : String
    measuredDependencyOrExitLoss : String

-- No generic promotion from an authored proposal to a realised effect.
-- Empty promotion-witness types are explicit safety gates, not evidence
-- that capture can never occur or that every actor acts in good faith.

data PublicAdvocacyAutomaticallyProvesCapture : Set where
data IncidentsAutomaticallyProveFabrication : Set where
data StructuralBenefitAutomaticallyProvesSharedIntent : Set where
data ProfitAutomaticallyProvesSustainability : Set where

advocacyNeedsOutcomeReceipt :
  PublicAdvocacyAutomaticallyProvesCapture → ⊥
advocacyNeedsOutcomeReceipt ()

realIncidentDoesNotProveManufacture :
  IncidentsAutomaticallyProveFabrication → ⊥
realIncidentDoesNotProveManufacture ()

structuralBenefitDoesNotRevealMotive :
  StructuralBenefitAutomaticallyProvesSharedIntent → ⊥
structuralBenefitDoesNotRevealMotive ()

supplierProfitDoesNotProveLabRecovery :
  ProfitAutomaticallyProvesSustainability → ⊥
supplierProfitDoesNotProveSustainability ()

existingMoat : Moat.RegulatoryMoatReceipt
existingMoat = Moat.canonicalStructuralMoatWithoutIntent

independentKnowledgeCut : Knowledge.TwoRoutesOneController
independentKnowledgeCut = Knowledge.canonicalSharedCut

darioProposalSource : Atlas.SourceReceipt
darioProposalSource = Atlas.darioPolicyJune2026

anthropicFiledCashAndCompute : Atlas.SourceReceipt
anthropicFiledCashAndCompute = Atlas.anthropicSECRegistration

project2025Precedent : Atlas.SourceReceipt
project2025Precedent = Atlas.heritagePolicy2025Defense

-- Counterfactual discriminator:
-- identical high-level safety justification + unequal compliance burdens
-- must be checked against real policy and available alternatives. A system's
-- realised effect remains distinct from a speaker's purported subjective aim.
------------------------------------------------------------------------
