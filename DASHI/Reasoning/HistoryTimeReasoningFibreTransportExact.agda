module DASHI.Reasoning.HistoryTimeReasoningFibreTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.HistoryTimeRelationalReasoningFibreExact as Fibre

------------------------------------------------------------------------
-- TYPED TRANSPORT OVER THE RELATIONAL REASONING FIBRE
--
-- A transition may alter only coordinates licensed by its transition kind.
-- Every unlicensed coordinate must be preserved literally. This makes
-- "everything stays attached" operational across time rather than merely
-- descriptive at each point.
------------------------------------------------------------------------

data Coordinate : Set where
  sourceCoordinate
  parserCoordinate
  semanticCoordinate
  pnfCoordinate
  logicalContextCoordinate
  derivationCoordinate
  consumerCoordinate
  coneCoordinate
  obligationsCoordinate
  residueCoordinate
  provenanceCoordinate
  : Coordinate

data TransitionKind : Set where
  sourceCorrection
  parserCorrection
  semanticRefinement
  pnfRevision
  empiricalEvidenceUpdate
  consumerRevision
  governanceRevision
  : TransitionKind

data MayChange : TransitionKind → Coordinate → Set where
  sourceMayChange : MayChange sourceCorrection sourceCoordinate
  sourceMayChangeParser : MayChange sourceCorrection parserCoordinate
  sourceMayChangeSemantic : MayChange sourceCorrection semanticCoordinate
  sourceMayChangePNF : MayChange sourceCorrection pnfCoordinate
  sourceMayChangeDerivation : MayChange sourceCorrection derivationCoordinate
  sourceMayChangeCone : MayChange sourceCorrection coneCoordinate
  sourceMayChangeObligations : MayChange sourceCorrection obligationsCoordinate
  sourceMayChangeResidue : MayChange sourceCorrection residueCoordinate

  parserMayChange : MayChange parserCorrection parserCoordinate
  parserMayChangeSemantic : MayChange parserCorrection semanticCoordinate
  parserMayChangePNF : MayChange parserCorrection pnfCoordinate
  parserMayChangeDerivation : MayChange parserCorrection derivationCoordinate
  parserMayChangeCone : MayChange parserCorrection coneCoordinate
  parserMayChangeObligations : MayChange parserCorrection obligationsCoordinate
  parserMayChangeResidue : MayChange parserCorrection residueCoordinate

  semanticMayChange : MayChange semanticRefinement semanticCoordinate
  semanticMayChangePNF : MayChange semanticRefinement pnfCoordinate
  semanticMayChangeDerivation : MayChange semanticRefinement derivationCoordinate
  semanticMayChangeCone : MayChange semanticRefinement coneCoordinate
  semanticMayChangeObligations : MayChange semanticRefinement obligationsCoordinate
  semanticMayChangeResidue : MayChange semanticRefinement residueCoordinate

  pnfMayChange : MayChange pnfRevision pnfCoordinate
  pnfMayChangeDerivation : MayChange pnfRevision derivationCoordinate
  pnfMayChangeCone : MayChange pnfRevision coneCoordinate
  pnfMayChangeObligations : MayChange pnfRevision obligationsCoordinate
  pnfMayChangeResidue : MayChange pnfRevision residueCoordinate

  evidenceMayChangeDerivation : MayChange empiricalEvidenceUpdate derivationCoordinate
  evidenceMayChangeCone : MayChange empiricalEvidenceUpdate coneCoordinate
  evidenceMayChangeObligations : MayChange empiricalEvidenceUpdate obligationsCoordinate
  evidenceMayChangeResidue : MayChange empiricalEvidenceUpdate residueCoordinate
  evidenceMayChangeProvenance : MayChange empiricalEvidenceUpdate provenanceCoordinate

  consumerMayChange : MayChange consumerRevision consumerCoordinate
  consumerMayChangeCone : MayChange consumerRevision coneCoordinate
  consumerMayChangeObligations : MayChange consumerRevision obligationsCoordinate
  consumerMayChangeResidue : MayChange consumerRevision residueCoordinate

  governanceMayChangeConsumer : MayChange governanceRevision consumerCoordinate
  governanceMayChangeCone : MayChange governanceRevision coneCoordinate
  governanceMayChangeObligations : MayChange governanceRevision obligationsCoordinate
  governanceMayChangeResidue : MayChange governanceRevision residueCoordinate
  governanceMayChangeProvenance : MayChange governanceRevision provenanceCoordinate

coordinateValue :
  ∀ {carrier} → Coordinate → Fibre.ReasoningFibrePoint carrier → Fibre.Artifact carrier
coordinateValue sourceCoordinate = Fibre.sourceSurface
coordinateValue parserCoordinate = Fibre.parserState
coordinateValue semanticCoordinate = Fibre.semanticFibre
coordinateValue pnfCoordinate = Fibre.evidentialPNF
coordinateValue logicalContextCoordinate = Fibre.logicalContext
coordinateValue derivationCoordinate = Fibre.derivationState
coordinateValue consumerCoordinate = Fibre.consumerState
coordinateValue coneCoordinate = Fibre.implicationCone
coordinateValue obligationsCoordinate = Fibre.openObligations
coordinateValue residueCoordinate = Fibre.historyResidue
coordinateValue provenanceCoordinate = Fibre.provenanceAuthority

record GovernedFibreTransport
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    (kind : TransitionKind)
    (before after : Fibre.ReasoningFibrePoint carrier) : Set₁ where
  constructor governedFibreTransport
  field
    sameHistory : Fibre.pointHistory after ≡ Fibre.pointHistory before
    preservesOutsideDeclaredChange :
      (coordinate : Coordinate) →
      (MayChange kind coordinate → ⊥) →
      coordinateValue coordinate after ≡ coordinateValue coordinate before
    transitionAuthorityReference : String
    retainedAttachmentReference : String
    changedCoordinateReference : String

open GovernedFibreTransport public

producerSemanticRefinementCannotChangeConsumer :
  ∀ {carrier before after} →
  GovernedFibreTransport semanticRefinement {carrier = carrier} before after →
  Fibre.consumerState after ≡ Fibre.consumerState before
producerSemanticRefinementCannotChangeConsumer transport =
  preservesOutsideDeclaredChange transport consumerCoordinate (λ ())

pnfRevisionCannotChangeConsumer :
  ∀ {carrier before after} →
  GovernedFibreTransport pnfRevision {carrier = carrier} before after →
  Fibre.consumerState after ≡ Fibre.consumerState before
pnfRevisionCannotChangeConsumer transport =
  preservesOutsideDeclaredChange transport consumerCoordinate (λ ())

consumerRevisionCannotRewriteSource :
  ∀ {carrier before after} →
  GovernedFibreTransport consumerRevision {carrier = carrier} before after →
  Fibre.sourceSurface after ≡ Fibre.sourceSurface before
consumerRevisionCannotRewriteSource transport =
  preservesOutsideDeclaredChange transport sourceCoordinate (λ ())

consumerRevisionCannotRewriteParser :
  ∀ {carrier before after} →
  GovernedFibreTransport consumerRevision {carrier = carrier} before after →
  Fibre.parserState after ≡ Fibre.parserState before
consumerRevisionCannotRewriteParser transport =
  preservesOutsideDeclaredChange transport parserCoordinate (λ ())

consumerRevisionCannotRewritePNF :
  ∀ {carrier before after} →
  GovernedFibreTransport consumerRevision {carrier = carrier} before after →
  Fibre.evidentialPNF after ≡ Fibre.evidentialPNF before
consumerRevisionCannotRewritePNF transport =
  preservesOutsideDeclaredChange transport pnfCoordinate (λ ())

empiricalEvidenceCannotRewriteSource :
  ∀ {carrier before after} →
  GovernedFibreTransport empiricalEvidenceUpdate {carrier = carrier} before after →
  Fibre.sourceSurface after ≡ Fibre.sourceSurface before
empiricalEvidenceCannotRewriteSource transport =
  preservesOutsideDeclaredChange transport sourceCoordinate (λ ())

record HistoryTimeReasoningFibreTransportBoundary : Set where
  constructor historyTimeReasoningFibreTransportBoundary
  field
    transitionMayAlterAnyCoordinateItWants : Bool
    transitionMayAlterAnyCoordinateItWantsIsFalse :
      transitionMayAlterAnyCoordinateItWants ≡ false
    semanticRefinementMaySilentlyRewriteConsumer : Bool
    semanticRefinementMaySilentlyRewriteConsumerIsFalse :
      semanticRefinementMaySilentlyRewriteConsumer ≡ false
    consumerRevisionMayRewriteSourceHistory : Bool
    consumerRevisionMayRewriteSourceHistoryIsFalse :
      consumerRevisionMayRewriteSourceHistory ≡ false
    empiricalEvidenceMayRewriteSourceText : Bool
    empiricalEvidenceMayRewriteSourceTextIsFalse :
      empiricalEvidenceMayRewriteSourceText ≡ false
    transportRetainsAttachmentReference : Bool
    transportRetainsAttachmentReferenceIsTrue :
      transportRetainsAttachmentReference ≡ true

canonicalHistoryTimeReasoningFibreTransportBoundary :
  HistoryTimeReasoningFibreTransportBoundary
canonicalHistoryTimeReasoningFibreTransportBoundary =
  historyTimeReasoningFibreTransportBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
