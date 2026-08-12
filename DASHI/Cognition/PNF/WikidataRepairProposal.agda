module DASHI.Cognition.PNF.WikidataRepairProposal where

open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.BoundedExecutionCarrier as Bounded
import DASHI.Cognition.PNF.TypePressure as Pressure

------------------------------------------------------------------------
-- Reviewable ontology-repair targets.
------------------------------------------------------------------------

data RepairTarget : Set where
  objectTarget : ObjectId → RepairTarget
  typeEdgeTarget : ObjectId → SymbolId → RepairTarget
  relationEdgeTarget : ObjectId → SymbolId → ObjectId → RepairTarget

data RepairOperation : Set where
  splitEntity : RepairOperation
  underspecifyType : RepairOperation
  removeBadSuperclass : RepairOperation
  proposeLatentType : RepairOperation
  holdForReview : RepairOperation

record RepairEvidence : Set where
  constructor repairEvidence
  field
    signedPressure : ℤ
    factorWitnesses : List FactorId
    demandWitnesses : List DemandId
    residualNote : String
    provenance : String
    scope : String

open RepairEvidence public

record RepairProposal : Set where
  constructor repairProposal
  field
    target : RepairTarget
    operation : RepairOperation
    evidence : RepairEvidence

open RepairProposal public

------------------------------------------------------------------------
-- Direct adapter from a numeric predicate-role pressure witness.  The adapter
-- retains the exact signed pressure and originating factor; choosing a repair
-- operation remains an explicit policy decision.
------------------------------------------------------------------------

repairEvidenceFromRolePressure :
  ∀ {subject candidateType} →
  Pressure.NumericPredicateRolePressure subject candidateType →
  String → RepairEvidence
repairEvidenceFromRolePressure pressure residual =
  repairEvidence
    (Pressure.signedRolePressure pressure)
    (Pressure.factor pressure ∷ [])
    []
    residual
    (Pressure.pressureProvenance pressure)
    (Pressure.pressureScope pressure)

------------------------------------------------------------------------
-- A domain projector emits a bounded carrier of proposals.  This is the exact
-- endpoint sketched in the Wikidata presentation: local pressure/residual
-- analysis narrows the repair surface for review rather than globally solving
-- or rewriting Wikidata.
------------------------------------------------------------------------

record DomainRepairProjector : Set₁ where
  constructor domainRepairProjector
  field
    proposeRepairs : ObjectId → Bounded.BoundedExecutionCarrier RepairProposal

open DomainRepairProjector public

data RepairProposalAuthority : Set where
  proposalForReviewOnly : RepairProposalAuthority

data RepairProposalTruthPermission : RepairProposalAuthority → Set where

repairProposalCannotAssertOntologyTruth :
  RepairProposalTruthPermission proposalForReviewOnly → ⊥
repairProposalCannotAssertOntologyTruth ()

record WikidataRepairBoundary : Set where
  constructor wikidataRepairBoundary
  field
    boundedRepairListHasSemanticAuthority :
      Bounded.OverflowSemanticPermission Bounded.executionEvidenceOnly → ⊥
    proposalCannotPromoteOntologyTruth :
      RepairProposalTruthPermission proposalForReviewOnly → ⊥
    pressureCannotPromoteType : Pressure.TypePressurePromotionPermission → ⊥

open WikidataRepairBoundary public

canonicalWikidataRepairBoundary : WikidataRepairBoundary
canonicalWikidataRepairBoundary =
  wikidataRepairBoundary
    Bounded.executionOverflowHasNoSemanticPermission
    repairProposalCannotAssertOntologyTruth
    Pressure.pressureAloneCannotAssertType
