module DASHI.Governance.LombardiNarrativeStructureAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy

------------------------------------------------------------------------
-- LOMBARDI NARRATIVE-STRUCTURE ADAPTER
--
-- A narrative structure is a coarse consumer view over evidence-bearing
-- historical relations. It is not an alternate evidence calculus.
------------------------------------------------------------------------

data ObservationClass : Set where
  directEvidence : ObservationClass
  derivedPath : ObservationClass
  artisticRepresentation : ObservationClass

data EdgeStatus : Set where
  confirmed : EdgeStatus
  contested : EdgeStatus
  unresolved : EdgeStatus

data VisibleRelation : Set where
  visibleConnection : VisibleRelation
  visibleControl : VisibleRelation
  visibleTransfer : VisibleRelation

record FineNarrativeEdge : Set where
  constructor fine-edge
  field
    sourceLabel targetLabel : String
    canonicalRelation : Genealogy.PathwayRelation
    grade : Genealogy.EvidenceGrade
    provenance : String
    interval : String
    status : EdgeStatus
    observation : ObservationClass
    visible : VisibleRelation
open FineNarrativeEdge public

record CoarseNarrativeEdge : Set where
  constructor coarse-edge
  field
    coarseSourceLabel coarseTargetLabel : String
    coarseVisible : VisibleRelation
open CoarseNarrativeEdge public

project : FineNarrativeEdge → CoarseNarrativeEdge
project e = coarse-edge (FineNarrativeEdge.sourceLabel e) (FineNarrativeEdge.targetLabel e) (FineNarrativeEdge.visible e)

------------------------------------------------------------------------
-- Collision witness: two genuinely different fine archival states project to
-- the same coarse visible edge.
------------------------------------------------------------------------

fineConfirmedDirect : FineNarrativeEdge
fineConfirmedDirect = fine-edge
  "A" "B"
  Genealogy.directDocumentedTransfer
  Genealogy.gradeA
  "primary archival receipt"
  "1900-1901"
  confirmed
  directEvidence
  visibleConnection

fineContestedArtwork : FineNarrativeEdge
fineContestedArtwork = fine-edge
  "A" "B"
  Genealogy.analogyOnly
  Genealogy.gradeE
  "artwork-only representation"
  "represented interval"
  contested
  artisticRepresentation
  visibleConnection

fineStatesDiffer : fineConfirmedDirect ≡ fineContestedArtwork → ⊥
fineStatesDiffer ()

coarseCollision : project fineConfirmedDirect ≡ project fineContestedArtwork
coarseCollision = refl

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data VisualAdjacencyCreatesCausalLink : Set where
data GraphPathCreatesCausalChain : Set where
data NodeDegreeCreatesCulpability : Set where
data VisualCentralityCreatesCommandAuthority : Set where
data SharedCounterpartyCreatesCoordination : Set where
data SamePersonCreatesInstitutionalIdentity : Set where
data ArtworkRepresentationCreatesHistoricalReceipt : Set where

visualAdjacencyDoesNotCreateCausalLink : VisualAdjacencyCreatesCausalLink → ⊥
visualAdjacencyDoesNotCreateCausalLink ()

graphPathDoesNotCreateCausalChain : GraphPathCreatesCausalChain → ⊥
graphPathDoesNotCreateCausalChain ()

nodeDegreeDoesNotCreateCulpability : NodeDegreeCreatesCulpability → ⊥
nodeDegreeDoesNotCreateCulpability ()

visualCentralityDoesNotCreateCommandAuthority : VisualCentralityCreatesCommandAuthority → ⊥
visualCentralityDoesNotCreateCommandAuthority ()

sharedCounterpartyDoesNotCreateCoordination : SharedCounterpartyCreatesCoordination → ⊥
sharedCounterpartyDoesNotCreateCoordination ()

samePersonDoesNotCreateInstitutionalIdentity : SamePersonCreatesInstitutionalIdentity → ⊥
samePersonDoesNotCreateInstitutionalIdentity ()

artworkRepresentationDoesNotCreateHistoricalReceipt : ArtworkRepresentationCreatesHistoricalReceipt → ⊥
artworkRepresentationDoesNotCreateHistoricalReceipt ()

record NarrativeBoundary : Set where
  constructor narrative-boundary
  field
    diagramCompleteByDefault : Bool
    visualAdjacencyEqualsCausation : Bool
    graphPathEqualsCausalChain : Bool
    degreeEqualsCulpability : Bool
    centralityEqualsCommand : Bool
    artworkEqualsReceipt : Bool
    fineProvenanceRetained : Bool
open NarrativeBoundary public

canonicalNarrativeBoundary : NarrativeBoundary
canonicalNarrativeBoundary = narrative-boundary false false false false false false true
