module DASHI.Reasoning.PNFRevisionSelectiveReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as Event
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Reasoning.SemanticLogicalSelectiveReopeningExact as Reopen

------------------------------------------------------------------------
-- PNF REVISION LINEAGE -> SELECTIVE REOPENING
--
-- EventAlgebra already preserves the old PNF version under revision.  The
-- semantic/logical reopening owner already knows which dependent certificates
-- must be reconsidered.  This adapter joins those two canonical surfaces.
-- Obsolescence therefore does not mean deletion or refutation.
------------------------------------------------------------------------

data RevisionImpact : Set where
  parserSurfaceRevision
  semanticInterpretationRevision
  evidentialStrengthRevision
  contextRevision
  supersessionImpact
  : RevisionImpact

impactOf : Event.RevisionKind → RevisionImpact
impactOf Event.parserCorrection = parserSurfaceRevision
impactOf Event.entityResolutionCorrection = semanticInterpretationRevision
impactOf Event.translationRevision = semanticInterpretationRevision
impactOf Event.legalReclassification = contextRevision
impactOf Event.evidenceStrengthening = evidentialStrengthRevision
impactOf Event.evidenceWeakening = evidentialStrengthRevision
impactOf Event.contextualRevaluation = contextRevision
impactOf Event.contradictionRevision = evidentialStrengthRevision
impactOf Event.supersessionRevision = supersessionImpact
impactOf Event.promotionRevision = evidentialStrengthRevision
impactOf Event.demotionRevision = evidentialStrengthRevision

record VersionedPNFRevision : Set₁ where
  constructor versionedPNFRevision
  field
    revision : Event.PNFRevision
    oldVersionStillRetained : Event.oldVersionRetained revision ≡ true
    revisionImpact : RevisionImpact
    impactMatchesRevisionKind : revisionImpact ≡ impactOf (Event.revisionKind revision)
    lineageReference : String
    downstreamAuditReference : String

open VersionedPNFRevision public

------------------------------------------------------------------------
-- A semantic interpretation revision reuses the canonical transitive reopening
-- path.  The previous derivation remains a historical artifact but becomes
-- stale for current use until re-audited.
------------------------------------------------------------------------

record SemanticRevisionReopening
    (revision : VersionedPNFRevision) : Set₁ where
  constructor semanticRevisionReopening
  field
    isSemanticRevision : revisionImpact revision ≡ semanticInterpretationRevision
    pnfReopens :
      Dependency.ReopeningObligation
        Reopen.Depends
        Reopen.semanticResolutionCertificate
        Reopen.evidentialPNFCertificate
    derivationReopens :
      Dependency.ReopeningObligation
        Reopen.Depends
        Reopen.semanticResolutionCertificate
        Reopen.logicalDerivationCertificate
    coneReopens :
      Dependency.ReopeningObligation
        Reopen.Depends
        Reopen.semanticResolutionCertificate
        Reopen.implicationConeCertificate
    reopeningReference : String

open SemanticRevisionReopening public

canonicalSemanticRevisionReopening :
  (revision : VersionedPNFRevision) →
  revisionImpact revision ≡ semanticInterpretationRevision →
  SemanticRevisionReopening revision
canonicalSemanticRevisionReopening revision semantic =
  semanticRevisionReopening
    semantic
    Reopen.semanticToPNFReopening
    Reopen.semanticChangeReopensLogicalDerivation
    Reopen.semanticChangeReopensImplicationCone
    "PNF revision -> selective downstream semantic/logical/cone reopening"

------------------------------------------------------------------------
-- Status vocabulary keeps three notions separate.
------------------------------------------------------------------------

data HistoricalDerivationStatus : Set where
  currentDerivation
  stalePendingReaudit
  refutedDerivation
  : HistoricalDerivationStatus

staleIsNotRefuted : stalePendingReaudit ≡ refutedDerivation → ⊥
staleIsNotRefuted ()

staleIsNotDeleted : Set
staleIsNotDeleted = ⊤

retainedRevisionGivesHistoricalAvailability :
  (revision : VersionedPNFRevision) → ⊤
retainedRevisionGivesHistoricalAvailability revision = tt

record PNFRevisionReopeningBoundary : Set where
  constructor pnfRevisionReopeningBoundary
  field
    revisionDeletesOldVersion : Bool
    revisionDeletesOldVersionIsFalse : revisionDeletesOldVersion ≡ false
    staleDerivationEqualsRefutedDerivation : Bool
    staleDerivationEqualsRefutedDerivationIsFalse :
      staleDerivationEqualsRefutedDerivation ≡ false
    semanticRevisionMayReopenDownstreamDerivation : Bool
    semanticRevisionMayReopenDownstreamDerivationIsTrue :
      semanticRevisionMayReopenDownstreamDerivation ≡ true
    semanticRevisionMayReopenImplicationConeTransitively : Bool
    semanticRevisionMayReopenImplicationConeTransitivelyIsTrue :
      semanticRevisionMayReopenImplicationConeTransitively ≡ true
    historicalVersionRemainsInspectable : Bool
    historicalVersionRemainsInspectableIsTrue :
      historicalVersionRemainsInspectable ≡ true

canonicalPNFRevisionReopeningBoundary : PNFRevisionReopeningBoundary
canonicalPNFRevisionReopeningBoundary =
  pnfRevisionReopeningBoundary false refl false refl true refl true refl true refl
