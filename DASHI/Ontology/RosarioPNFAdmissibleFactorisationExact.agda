module DASHI.Ontology.RosarioPNFAdmissibleFactorisationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)

import DASHI.Cognition.PNF.TypePressure as PNFPressure
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Admission
import DASHI.Core.QueryFactorisationSufficiency as Factor
open import DASHI.Ontology.RosarioConceptualDiagnosticsExact

------------------------------------------------------------------------
-- DASHI CROSS-POLLINATION, NOT ATTRIBUTED TO ROSARIO
--
-- Rosario et al. supply the benchmark, measured LLM disagreement, hotspot
-- analysis, and KG-curation/refinement direction.  This module is DASHI's local
-- governance weld:
--
--   Rosario hotspot observation
--     -> explicit PNF interpretation
--     -> signed pressure / residual evidence
--     -> hard Admissible + ConsumerAdequate gate
--     -> consumer/query-specific FactorsThrough receipt
--     -> review-only repair proposal lane
--
-- The source does not claim PNF, `Admissible`, `ConsumerAdequate`,
-- `FactorsThrough`, or the local repair authority rules.
------------------------------------------------------------------------

record RosarioPNFInterpretation (observation : HotspotObservation) : Set where
  constructor rosarioPNFInterpretation
  field
    interpretedPressure : ℤ
    interpretationProvenance : String
    interpretationScope : String

open RosarioPNFInterpretation public

asHotspotPressure :
  {observation : HotspotObservation} →
  RosarioPNFInterpretation observation →
  PNFPressure.TypePressureContribution
    {Subject = BenchmarkDomain}
    {CandidateType = HotspotDisposition}
    {Evidence = HotspotObservation}
    (domain observation)
    (disposition observation)
asHotspotPressure {observation} interpretation =
  PNFPressure.typePressureContribution
    observation
    (interpretedPressure interpretation)
    (interpretationProvenance interpretation)
    (interpretationScope interpretation)

hotspotEvidencePreserved :
  {observation : HotspotObservation}
  (interpretation : RosarioPNFInterpretation observation) →
  PNFPressure.evidence (asHotspotPressure interpretation) ≡ observation
hotspotEvidencePreserved interpretation = refl

hotspotPressurePreserved :
  {observation : HotspotObservation}
  (interpretation : RosarioPNFInterpretation observation) →
  PNFPressure.signedPressure (asHotspotPressure interpretation)
  ≡ interpretedPressure interpretation
hotspotPressurePreserved interpretation = refl

hotspotProvenancePreserved :
  {observation : HotspotObservation}
  (interpretation : RosarioPNFInterpretation observation) →
  PNFPressure.provenance (asHotspotPressure interpretation)
  ≡ interpretationProvenance interpretation
hotspotProvenancePreserved interpretation = refl

------------------------------------------------------------------------
-- HOTSPOT SIGNAL != SIGN / MAGNITUDE / TRUTH
------------------------------------------------------------------------

data HotspotDeterminesPressurePermission : Set where

data HotspotDeterminesTruthPermission : Set where

hotspotDoesNotDeterminePressure : HotspotDeterminesPressurePermission → ⊥
hotspotDoesNotDeterminePressure ()

hotspotDoesNotDetermineTruth : HotspotDeterminesTruthPermission → ⊥
hotspotDoesNotDetermineTruth ()

hotspotPressureCannotAssertType :
  PNFPressure.TypePressurePromotionPermission → ⊥
hotspotPressureCannotAssertType = PNFPressure.pressureAloneCannotAssertType

------------------------------------------------------------------------
-- REPAIR ROUTING
------------------------------------------------------------------------

llmOnlyRoute : HotspotSignal → Repair.RepairOperation
llmOnlyRoute consistentClusterDisagreement = Repair.holdForReview
llmOnlyRoute highEdgeDisagreementRate = Repair.holdForReview
llmOnlyRoute crossModelConcentratedDisagreement = Repair.holdForReview

data LLMOnlyDestructiveRepairPermission : Set where

llmOnlyCannotAuthorizeDestructiveRepair :
  LLMOnlyDestructiveRepairPermission → ⊥
llmOnlyCannotAuthorizeDestructiveRepair ()

repairProposalReviewAuthority : Repair.RepairProposalAuthority
repairProposalReviewAuthority = Repair.proposalForReviewOnly

repairProposalStillCannotAssertTruth :
  Repair.RepairProposalTruthPermission Repair.proposalForReviewOnly → ⊥
repairProposalStillCannotAssertTruth = Repair.repairProposalCannotAssertOntologyTruth

------------------------------------------------------------------------
-- EXISTING ADMISSIBILITY + FACTORISATION SPINE
------------------------------------------------------------------------

record GovernedConsumerUse
    {State Surface Query : Set}
    (questions : Factor.InquiryQuestionFamily State Query)
    (project : State → Surface)
    (query : Query)
    (problem : Admission.ConsumerMDLProblem)
    (candidate : Admission.Model problem) : Set₁ where
  constructor governedConsumerUse
  field
    admissibleReceipt : Admission.Admissible problem candidate
    consumerAdequacyReceipt : Admission.ConsumerAdequate problem candidate
    factorisationReceipt : Factor.FactorsThrough questions project query
    reviewReference : String

open GovernedConsumerUse public

------------------------------------------------------------------------
-- FINITE FACTORISATION COUNTERMODEL
--
-- The same coarse mapping surface preserves the subclass answer but erases a
-- distinction needed by the disjointness consumer.  This is the repo-native
-- exact form of "safe for one inference language does not imply safe for all".
------------------------------------------------------------------------

data AlignmentState : Set where
  leftAlignmentState : AlignmentState
  rightAlignmentState : AlignmentState

data AlignmentSurface : Set where
  coarseAlignment : AlignmentSurface

data AlignmentQuery : Set where
  subclassQuery : AlignmentQuery
  disjointnessQuery : AlignmentQuery

data AlignmentAnswer : Set where
  subclassKnown : AlignmentAnswer
  disjointYes : AlignmentAnswer
  disjointNo : AlignmentAnswer

alignmentQuestions : Factor.InquiryQuestionFamily AlignmentState AlignmentQuery
alignmentQuestions = Factor.inquiryQuestionFamily (λ query → AlignmentAnswer) askAlignment
  where
    askAlignment : (query : AlignmentQuery) → AlignmentState → AlignmentAnswer
    askAlignment subclassQuery leftAlignmentState = subclassKnown
    askAlignment subclassQuery rightAlignmentState = subclassKnown
    askAlignment disjointnessQuery leftAlignmentState = disjointYes
    askAlignment disjointnessQuery rightAlignmentState = disjointNo

coarseAlignmentSurface : AlignmentState → AlignmentSurface
coarseAlignmentSurface leftAlignmentState = coarseAlignment
coarseAlignmentSurface rightAlignmentState = coarseAlignment

subclassFactorsThrough :
  Factor.FactorsThrough alignmentQuestions coarseAlignmentSurface subclassQuery
subclassFactorsThrough = Factor.factorsThrough quotient proof
  where
    quotient : AlignmentSurface → AlignmentAnswer
    quotient coarseAlignment = subclassKnown

    proof :
      (state : AlignmentState) →
      Factor.ask alignmentQuestions subclassQuery state
      ≡ quotient (coarseAlignmentSurface state)
    proof leftAlignmentState = refl
    proof rightAlignmentState = refl

disjointnessCannotFactorThrough :
  Factor.FactorsThrough alignmentQuestions coarseAlignmentSurface disjointnessQuery → ⊥
disjointnessCannotFactorThrough receipt
  with Factor.factorisation receipt leftAlignmentState
     | Factor.factorisation receipt rightAlignmentState
... | refl | ()

------------------------------------------------------------------------
-- GOVERNANCE STATUS
------------------------------------------------------------------------

record RepairUseBoundary : Set where
  constructor repairUseBoundary
  field
    llmSignalAloneIsEditAuthority : Bool
    pnfPressureAloneIsOntologyTruth : Bool
    admissibilityRequiredBeforeUse : Bool
    factorisationRequiredPerConsumerQuery : Bool
    finiteConsumerCountermodelOwned : Bool
    repairProposalIsReviewOnly : Bool

    llmSignalAloneIsEditAuthorityIsFalse :
      llmSignalAloneIsEditAuthority ≡ false
    pnfPressureAloneIsOntologyTruthIsFalse :
      pnfPressureAloneIsOntologyTruth ≡ false
    admissibilityRequiredBeforeUseIsTrue :
      admissibilityRequiredBeforeUse ≡ true
    factorisationRequiredPerConsumerQueryIsTrue :
      factorisationRequiredPerConsumerQuery ≡ true
    finiteConsumerCountermodelOwnedIsTrue : finiteConsumerCountermodelOwned ≡ true
    repairProposalIsReviewOnlyIsTrue : repairProposalIsReviewOnly ≡ true

open RepairUseBoundary public

canonicalRepairUseBoundary : RepairUseBoundary
canonicalRepairUseBoundary =
  repairUseBoundary
    false false true true true true
    refl refl refl refl refl refl
