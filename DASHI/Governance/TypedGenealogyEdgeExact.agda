module DASHI.Governance.TypedGenealogyEdgeExact where

------------------------------------------------------------------------
-- TWO-AXIS GENEALOGY EDGE
--
-- The relation asserted by an edge and the quality of evidence for that
-- relation are orthogonal.  A primary document can establish recurrence of a
-- technique without establishing historical transmission of that technique.
-- Conversely, a documented personnel-continuity edge need not assert method
-- transfer at all.
--
-- This module is a DASHI evidence-calculus construction.  It cross-pollinates
-- EvidenceGradedGenealogyCore without changing the meaning of its existing
-- EvidenceEdge / StrongEvidenceEdge API.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.EvidenceGradedGenealogyCore as Legacy

------------------------------------------------------------------------
-- Relation kind: what proposition the edge asserts.
------------------------------------------------------------------------

data RelationKind : Set where
  directMethodTransfer : RelationKind
  historicalTransfer : RelationKind
  funding : RelationKind
  personnelContinuity : RelationKind
  organisationalContinuity : RelationKind
  methodRecurrence : RelationKind
  specificMethodTransfer : RelationKind
  audienceAdjacency : RelationKind
  recommendationExposure : RelationKind
  conceptualBorrowing : RelationKind
  analogy : RelationKind

------------------------------------------------------------------------
-- Evidence strength: how strongly the installed sources support that exact
-- relation.  `pendingBridge` and `candidateUnresolved` are deliberately not
-- strong evidence classes.
------------------------------------------------------------------------

data EvidenceStrength : Set where
  primary : EvidenceStrength
  corroborated : EvidenceStrength
  secondary : EvidenceStrength
  pendingBridge : EvidenceStrength
  candidateUnresolved : EvidenceStrength
  analogyOnly : EvidenceStrength

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    authorOrInstitution : String
    title : String
    dateOrYear : String
    identifier : String
    boundedRole : String

open SourceReceipt public

record TypedGenealogyEdge : Set where
  constructor typedGenealogyEdge
  field
    edgeId : String
    fromNode : String
    toNode : String
    relationKind : RelationKind
    evidenceStrength : EvidenceStrength
    receipts : List SourceReceipt
    boundedClaim : String

open TypedGenealogyEdge public

------------------------------------------------------------------------
-- Historical-transfer semantics require BOTH an appropriate relation kind and
-- sufficiently strong evidence.  Primary evidence for a different relation
-- (for example method recurrence) cannot inhabit this witness.
------------------------------------------------------------------------

data TransferRelation : RelationKind → Set where
  directTransferRelation : TransferRelation directMethodTransfer
  historicalTransferRelation : TransferRelation historicalTransfer
  specificTransferRelation : TransferRelation specificMethodTransfer

data StrongEvidence : EvidenceStrength → Set where
  primaryStrong : StrongEvidence primary
  corroboratedStrong : StrongEvidence corroborated

record StrongHistoricalTransfer (edge : TypedGenealogyEdge) : Set where
  constructor strongHistoricalTransfer
  field
    relationIsTransfer : TransferRelation (relationKind edge)
    evidenceIsStrong : StrongEvidence (evidenceStrength edge)

open StrongHistoricalTransfer public

methodRecurrenceIsNotTransferRelation : TransferRelation methodRecurrence → ⊥
methodRecurrenceIsNotTransferRelation ()

fundingIsNotTransferRelation : TransferRelation funding → ⊥
fundingIsNotTransferRelation ()

personnelContinuityIsNotTransferRelation : TransferRelation personnelContinuity → ⊥
personnelContinuityIsNotTransferRelation ()

organisationalContinuityIsNotTransferRelation : TransferRelation organisationalContinuity → ⊥
organisationalContinuityIsNotTransferRelation ()

pendingBridgeIsNotStrong : StrongEvidence pendingBridge → ⊥
pendingBridgeIsNotStrong ()

candidateUnresolvedIsNotStrong : StrongEvidence candidateUnresolved → ⊥
candidateUnresolvedIsNotStrong ()

------------------------------------------------------------------------
-- Explicit no-go tokens: evidence quality does not rewrite relation semantics.
------------------------------------------------------------------------

data PrimaryRecurrencePromotesHistoricalTransfer : Set where

data CorroboratedFundingPromotesMethodTransfer : Set where

data RepeatedSecondaryAssertionResolvesCandidate : Set where

primaryRecurrenceDoesNotPromoteTransfer :
  PrimaryRecurrencePromotesHistoricalTransfer → ⊥
primaryRecurrenceDoesNotPromoteTransfer ()

fundingDoesNotPromoteMethodTransfer :
  CorroboratedFundingPromotesMethodTransfer → ⊥
fundingDoesNotPromoteMethodTransfer ()

repetitionDoesNotResolveCandidate :
  RepeatedSecondaryAssertionResolvesCandidate → ⊥
repetitionDoesNotResolveCandidate ()

record TypedGenealogyBoundary : Set where
  constructor typedGenealogyBoundary
  field
    relationAndEvidenceAreSeparateAxes : Bool
    primaryEvidenceCanSupportNonTransferRelation : Bool
    methodRecurrenceEqualsHistoricalTransfer : Bool
    unresolvedEqualsRefuted : Bool
    transferRequiresRelationAndEvidenceWitness : Bool
    legacyStrongEvidenceEdgeEqualsStrongHistoricalTransfer : Bool

canonicalTypedGenealogyBoundary : TypedGenealogyBoundary
canonicalTypedGenealogyBoundary =
  typedGenealogyBoundary true true false false true false
