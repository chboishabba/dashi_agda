module DASHI.Ontology.RosarioPNFAdmissibleFactorisationExact where

open import Agda.Builtin.Bool using (Bool; true)
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
--
-- LLM-only evidence may prioritize or hold a case for review.  It cannot by
-- itself choose a destructive ontology mutation.  Stronger repair operations
-- require additional symbolic/domain/human evidence and the downstream gates.
------------------------------------------------------------------------

llmOnlyRoute : HotspotSignal → Repair.RepairOperation
llmOnlyRoute consistentClusterDisagreement = Repair.holdForReview
llmOnlyRoute highEdgeDisagreementRate = Repair.holdForReview
llmOnlyRoute crossModelConcentratedDisagreement = Repair.holdForReview

data LLMOnlyDestructiveRepairPermission : Set where

llmOnlyCannotAuthorizeDestructiveRepair :
  LLMOnlyDestructiveRepairPermission → ⊥
llmOnlyCannotAuthorizeDestructiveRepair ()

repairProposalRemainsReviewOnly : Repair.RepairProposalAuthority
repairProposalRemainsReviewOnly = Repair.proposalForReviewOnly

repairProposalStillCannotAssertTruth :
  Repair.RepairProposalTruthPermission Repair.proposalForReviewOnly → ⊥
repairProposalStillCannotAssertTruth = Repair.repairProposalCannotAssertOntologyTruth

------------------------------------------------------------------------
-- EXISTING ADMISSIBILITY + FACTORISATION SPINE
--
-- No new SafeFor relation is introduced.  A consumer use is governed only when
-- the candidate is hard-admissible, adequate for that consumer, and the
-- authorised query literally factors through the proposed projection.
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

record RepairUseBoundary : Set where
  constructor repairUseBoundary
  field
    llmSignalAloneIsEditAuthority : Bool
    pnfPressureAloneIsOntologyTruth : Bool
    admissibilityRequiredBeforeUse : Bool
    factorisationRequiredPerConsumerQuery : Bool
    repairProposalRemainsReviewOnly : Bool

    llmSignalAloneIsEditAuthorityIsFalse : llmSignalAloneIsEditAuthority ≡ Bool.false
    pnfPressureAloneIsOntologyTruthIsFalse : pnfPressureAloneIsOntologyTruth ≡ Bool.false
    admissibilityRequiredBeforeUseIsTrue : admissibilityRequiredBeforeUse ≡ true
    factorisationRequiredPerConsumerQueryIsTrue :
      factorisationRequiredPerConsumerQuery ≡ true
    repairProposalRemainsReviewOnlyIsTrue : repairProposalRemainsReviewOnly ≡ true

------------------------------------------------------------------------
-- The Bool module is imported with true only above; use a small local false
-- alias through the builtin constructor to keep the status explicit.
------------------------------------------------------------------------
