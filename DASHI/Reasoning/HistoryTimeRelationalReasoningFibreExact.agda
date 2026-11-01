module DASHI.Reasoning.HistoryTimeRelationalReasoningFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as Consumer

------------------------------------------------------------------------
-- HISTORY/TIME RELATIONAL REASONING FIBRE
--
-- A reasoning state at (h,t) is not only a tuple of visible coordinates.
-- Every relevant artifact remains attached to its history/time point, and
-- cross-point relations retain justified lineage, reopening dependency, and
-- evidential/logical support as THREE DISTINCT relation families.
--
-- Attachment means proof-bearing reachability/lineage, not copying every
-- artifact into every downstream record.
------------------------------------------------------------------------

record HistoryTimeArtifactCarrier : Set₁ where
  constructor historyTimeArtifactCarrier
  field
    History : Set
    Time : Set
    Artifact : Set
    presentAt : History → Time → Artifact → Set
    carrierReference : String

open HistoryTimeArtifactCarrier public

record PointArtifact (carrier : HistoryTimeArtifactCarrier) : Set₁ where
  constructor pointArtifact
  field
    history : History carrier
    time : Time carrier
    artifact : Artifact carrier
    present : presentAt carrier history time artifact
    attachmentReference : String

open PointArtifact public

------------------------------------------------------------------------
-- Three non-collapsed attachment relations.
------------------------------------------------------------------------

record RelationalAttachmentFabric
    (carrier : HistoryTimeArtifactCarrier) : Set₂ where
  constructor relationalAttachmentFabric
  field
    DerivedFrom : PointArtifact carrier → PointArtifact carrier → Set
    Depends : PointArtifact carrier → PointArtifact carrier → Set
    Supports : PointArtifact carrier → PointArtifact carrier → Set

    lineageReading : String
    dependencyReading : String
    supportReading : String

open RelationalAttachmentFabric public

------------------------------------------------------------------------
-- A complete reasoning point keeps the important coordinates present at the
-- same (h,t). The artifact values need not be equal and need not duplicate one
-- another's payloads; their common point and relational fabric retain the
-- attachment structure.
------------------------------------------------------------------------

record ReasoningFibrePoint
    (carrier : HistoryTimeArtifactCarrier) : Set₁ where
  constructor reasoningFibrePoint
  field
    pointHistory : History carrier
    pointTime : Time carrier

    sourceSurface : Artifact carrier
    parserState : Artifact carrier
    semanticFibre : Artifact carrier
    evidentialPNF : Artifact carrier
    logicalContext : Artifact carrier
    derivationState : Artifact carrier
    consumerState : Artifact carrier
    implicationCone : Artifact carrier
    openObligations : Artifact carrier
    historyResidue : Artifact carrier
    provenanceAuthority : Artifact carrier

    sourcePresent : presentAt carrier pointHistory pointTime sourceSurface
    parserPresent : presentAt carrier pointHistory pointTime parserState
    semanticPresent : presentAt carrier pointHistory pointTime semanticFibre
    pnfPresent : presentAt carrier pointHistory pointTime evidentialPNF
    logicalContextPresent : presentAt carrier pointHistory pointTime logicalContext
    derivationPresent : presentAt carrier pointHistory pointTime derivationState
    consumerPresent : presentAt carrier pointHistory pointTime consumerState
    conePresent : presentAt carrier pointHistory pointTime implicationCone
    obligationsPresent : presentAt carrier pointHistory pointTime openObligations
    residuePresent : presentAt carrier pointHistory pointTime historyResidue
    provenancePresent : presentAt carrier pointHistory pointTime provenanceAuthority

    pointReference : String

open ReasoningFibrePoint public

atSource :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atSource point = pointArtifact
  (pointHistory point) (pointTime point) (sourceSurface point)
  (sourcePresent point) "source surface at reasoning fibre point"

atParser :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atParser point = pointArtifact
  (pointHistory point) (pointTime point) (parserState point)
  (parserPresent point) "parser state at reasoning fibre point"

atSemantic :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atSemantic point = pointArtifact
  (pointHistory point) (pointTime point) (semanticFibre point)
  (semanticPresent point) "semantic fibre at reasoning fibre point"

atPNF :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atPNF point = pointArtifact
  (pointHistory point) (pointTime point) (evidentialPNF point)
  (pnfPresent point) "evidential PNF at reasoning fibre point"

atDerivation :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atDerivation point = pointArtifact
  (pointHistory point) (pointTime point) (derivationState point)
  (derivationPresent point) "derivation state at reasoning fibre point"

atConsumer :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atConsumer point = pointArtifact
  (pointHistory point) (pointTime point) (consumerState point)
  (consumerPresent point) "consumer state at reasoning fibre point"

atCone :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atCone point = pointArtifact
  (pointHistory point) (pointTime point) (implicationCone point)
  (conePresent point) "implication cone at reasoning fibre point"

atObligations :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atObligations point = pointArtifact
  (pointHistory point) (pointTime point) (openObligations point)
  (obligationsPresent point) "open obligations at reasoning fibre point"

atResidue :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atResidue point = pointArtifact
  (pointHistory point) (pointTime point) (historyResidue point)
  (residuePresent point) "history residue at reasoning fibre point"

atProvenance :
  ∀ {carrier} → ReasoningFibrePoint carrier → PointArtifact carrier
atProvenance point = pointArtifact
  (pointHistory point) (pointTime point) (provenanceAuthority point)
  (provenancePresent point) "provenance/authority at reasoning fibre point"

------------------------------------------------------------------------
-- Point-local canonical attachment spine. This is a receipt, not an assertion
-- that these are the only relations in the fabric.
------------------------------------------------------------------------

record LocalReasoningAttachmentReceipt
    {carrier : HistoryTimeArtifactCarrier}
    (fabric : RelationalAttachmentFabric carrier)
    (point : ReasoningFibrePoint carrier) : Set₁ where
  constructor localReasoningAttachmentReceipt
  field
    sourceToParser : DerivedFrom fabric (atParser point) (atSource point)
    parserToSemantic : DerivedFrom fabric (atSemantic point) (atParser point)
    semanticToPNF : DerivedFrom fabric (atPNF point) (atSemantic point)
    pnfSupportsDerivation : Supports fabric (atPNF point) (atDerivation point)
    derivationSupportsCone : Supports fabric (atDerivation point) (atCone point)
    consumerConstrainsCone : Depends fabric (atConsumer point) (atCone point)
    semanticReopensDerivation : Depends fabric (atSemantic point) (atDerivation point)
    derivationReopensCone : Depends fabric (atDerivation point) (atCone point)
    provenanceRetainedWithDerivation : DerivedFrom fabric (atDerivation point) (atProvenance point)
    obligationsDependOnCone : Depends fabric (atCone point) (atObligations point)
    receiptReference : String

open LocalReasoningAttachmentReceipt public

------------------------------------------------------------------------
-- Reopening uses ONLY Depends. Lineage and support remain inspectable but do
-- not silently become invalidation edges.
------------------------------------------------------------------------

reopeningFromDependencyPath :
  ∀ {carrier}
    {fabric : RelationalAttachmentFabric carrier}
    {changed affected : PointArtifact carrier} →
  Dependency.AffectedClosure (Depends fabric) changed affected →
  Dependency.ReopeningObligation (Depends fabric) changed affected
reopeningFromDependencyPath path = Dependency.reopeningObligation path

record RelationSeparationWitness
    {carrier : HistoryTimeArtifactCarrier}
    (fabric : RelationalAttachmentFabric carrier) : Set₁ where
  constructor relationSeparationWitness
  field
    lineageOnlySource lineageOnlyTarget : PointArtifact carrier
    lineageOnly : DerivedFrom fabric lineageOnlySource lineageOnlyTarget
    lineageNotDependency : Depends fabric lineageOnlySource lineageOnlyTarget → ⊥

    dependencyOnlySource dependencyOnlyTarget : PointArtifact carrier
    dependencyOnly : Depends fabric dependencyOnlySource dependencyOnlyTarget
    dependencyNotSupport : Supports fabric dependencyOnlySource dependencyOnlyTarget → ⊥

    supportOnlySource supportOnlyTarget : PointArtifact carrier
    supportOnly : Supports fabric supportOnlySource supportOnlyTarget
    supportNotLineage : DerivedFrom fabric supportOnlySource supportOnlyTarget → ⊥

open RelationSeparationWitness public

------------------------------------------------------------------------
-- Consumer/time bridge. The fibre capstone may be paired with the canonical
-- history-time consumer surface; this keeps C_h(t) itself as a transported
-- coordinate rather than an external timeless observer.
------------------------------------------------------------------------

record RelationalConsumerFibreCapstone : Set₂ where
  constructor relationalConsumerFibreCapstone
  field
    artifactCarrier : HistoryTimeArtifactCarrier
    attachmentFabric : RelationalAttachmentFabric artifactCarrier
    consumerSurface : Consumer.HistoryTimeConsumerFibreSurface
    historyTypeAgrees : History artifactCarrier ≡ Consumer.History consumerSurface
    timeTypeAgrees : Time artifactCarrier ≡ Consumer.Time consumerSurface
    attachmentPolicyReference : String
    consumerVersionPolicyReference : String

open RelationalConsumerFibreCapstone public

------------------------------------------------------------------------
-- Hard boundary: keeping everything attached does not erase relation kinds.
------------------------------------------------------------------------

record HistoryTimeRelationalReasoningFibreBoundary : Set where
  constructor historyTimeRelationalReasoningFibreBoundary
  field
    relevantArtifactsRemainPointAttached : Bool
    relevantArtifactsRemainPointAttachedIsTrue :
      relevantArtifactsRemainPointAttached ≡ true
    attachmentRequiresPayloadDuplicationEverywhere : Bool
    attachmentRequiresPayloadDuplicationEverywhereIsFalse :
      attachmentRequiresPayloadDuplicationEverywhere ≡ false
    lineageEqualsReopeningDependency : Bool
    lineageEqualsReopeningDependencyIsFalse :
      lineageEqualsReopeningDependency ≡ false
    supportEqualsReopeningDependency : Bool
    supportEqualsReopeningDependencyIsFalse :
      supportEqualsReopeningDependency ≡ false
    dependencyByItselfProvesSupportedClaim : Bool
    dependencyByItselfProvesSupportedClaimIsFalse :
      dependencyByItselfProvesSupportedClaim ≡ false
    consumerIsInsideHistoryTimeFabric : Bool
    consumerIsInsideHistoryTimeFabricIsTrue :
      consumerIsInsideHistoryTimeFabric ≡ true

canonicalHistoryTimeRelationalReasoningFibreBoundary :
  HistoryTimeRelationalReasoningFibreBoundary
canonicalHistoryTimeRelationalReasoningFibreBoundary =
  historyTimeRelationalReasoningFibreBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
