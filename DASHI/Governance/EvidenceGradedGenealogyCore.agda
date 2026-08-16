module DASHI.Governance.EvidenceGradedGenealogyCore where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Authors: Naomi Oreskes; Erik M. Conway.
-- Title: "Merchants of Doubt: How a Handful of Scientists Obscured the Truth
-- on Issues from Tobacco Smoke to Global Warming".
-- Publisher: Bloomsbury Press, 2010.
-- ISBN: 978-1-59691-610-4. No DOI asserted for the book.
--
-- Authors: Naomi Oreskes; Erik M. Conway.
-- Title: "Defeating the merchants of doubt".
-- Venue: Nature 465:686--687 (2010).
-- DOI: 10.1038/465686a.
--
-- These sources motivate historical genealogy / recurring-actor / strategy
-- vocabulary.  The evidence-grade calculus below is a DASHI construction and
-- does not infer coordination, motive, radicalisation, or causality from mere
-- similarity or audience overlap.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- A compact evidence ladder.
--
-- A: direct documented transfer / explicit personnel or document continuity
-- B: documented institutional/personnel continuity across domains
-- C: bounded audience/content adjacency or co-occurrence
-- D: shared method or rhetoric without transfer evidence
-- E: analogy only
------------------------------------------------------------------------

data EvidenceGrade : Set where
  gradeA gradeB gradeC gradeD gradeE : EvidenceGrade

data PathwayRelation : Set where
  directDocumentedTransfer : PathwayRelation
  personnelInstitutionalContinuity : PathwayRelation
  fundingOrganisationalLink : PathwayRelation
  audienceContentAdjacency : PathwayRelation
  recommendationExposure : PathwayRelation
  conceptualBorrowing : PathwayRelation
  sharedMethodOnly : PathwayRelation
  analogyOnly : PathwayRelation

data NodeKind : Set where
  organisation person community technique narrative platform institution : NodeKind

record GenealogyNode : Set where
  constructor genealogyNode
  field
    label : String
    kind : NodeKind

open GenealogyNode public

record EvidenceEdge : Set₁ where
  constructor evidenceEdge
  field
    source target : GenealogyNode
    relation : PathwayRelation
    grade : EvidenceGrade
    sources : List Sources.ScholarlySource
    boundedClaim : String

open EvidenceEdge public

------------------------------------------------------------------------
-- Strong historical-genealogy edges are deliberately restricted to A/B.
------------------------------------------------------------------------

data StrongGrade : EvidenceGrade → Set where
  strongA : StrongGrade gradeA
  strongB : StrongGrade gradeB

record StrongEvidenceEdge (edge : EvidenceEdge) : Set where
  constructor strongEvidenceEdge
  field
    gradeStrong : StrongGrade (grade edge)

open StrongEvidenceEdge public

gradeCIsNotStrong : StrongGrade gradeC → ⊥
gradeCIsNotStrong ()

gradeDIsNotStrong : StrongGrade gradeD → ⊥
gradeDIsNotStrong ()

gradeEIsNotStrong : StrongGrade gradeE → ⊥
gradeEIsNotStrong ()

------------------------------------------------------------------------
-- Path composition keeps provenance edge-local.
------------------------------------------------------------------------

data EvidencePath : GenealogyNode → GenealogyNode → Set₁ where
  pathSingle :
    (edge : EvidenceEdge) →
    EvidencePath (source edge) (target edge)
  pathStep :
    ∀ {start middle finish} →
    (edge : EvidenceEdge) →
    source edge ≡ start →
    target edge ≡ middle →
    EvidencePath middle finish →
    EvidencePath start finish

record StrongEvidencePath (start finish : GenealogyNode) : Set₁ where
  constructor strongEvidencePath
  field
    path : EvidencePath start finish
    EveryStrong : Set
    everyStrong : EveryStrong

------------------------------------------------------------------------
-- Negative promotion tokens.
------------------------------------------------------------------------

data SharedRhetoricEstablishesCoordination : Set where

data AudienceOverlapEstablishesRadicalisation : Set where

data SimilarMethodEstablishesTransfer : Set where

data OneStrongEdgeEstablishesUniversalNetwork : Set where

sharedRhetoricDoesNotEstablishCoordination :
  SharedRhetoricEstablishesCoordination → ⊥
sharedRhetoricDoesNotEstablishCoordination ()

audienceOverlapDoesNotEstablishRadicalisation :
  AudienceOverlapEstablishesRadicalisation → ⊥
audienceOverlapDoesNotEstablishRadicalisation ()

similarMethodDoesNotEstablishTransfer :
  SimilarMethodEstablishesTransfer → ⊥
similarMethodDoesNotEstablishTransfer ()

oneStrongEdgeDoesNotEstablishUniversalNetwork :
  OneStrongEdgeEstablishesUniversalNetwork → ⊥
oneStrongEdgeDoesNotEstablishUniversalNetwork ()

record EvidenceGradedGenealogyBoundary : Set where
  constructor evidenceGradedGenealogyBoundary
  field
    directTransferAndAnalogyAreSeparated : Bool
    audienceAdjacencyEqualsCausalRadicalisation : Bool
    sharedRhetoricEqualsCoordination : Bool
    gradeAorBRequiredForStrongHistoricalEdge : Bool
    pathProvenanceRemainsEdgeLocal : Bool
    historicalContinuityEqualsCentralCommand : Bool

canonicalEvidenceGradedGenealogyBoundary : EvidenceGradedGenealogyBoundary
canonicalEvidenceGradedGenealogyBoundary =
  evidenceGradedGenealogyBoundary true false false true true false

record EvidenceGradedGenealogySourceReceipt : Set where
  constructor evidenceGradedGenealogySourceReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : EvidenceGradedGenealogyBoundary

canonicalEvidenceGradedGenealogySourceReceipt :
  EvidenceGradedGenealogySourceReceipt
canonicalEvidenceGradedGenealogySourceReceipt =
  evidenceGradedGenealogySourceReceipt
    (Sources.merchantsOfDoubtHistory
      ∷ Sources.oreskesConwayNatureCommentary
      ∷ [])
    canonicalEvidenceGradedGenealogyBoundary
