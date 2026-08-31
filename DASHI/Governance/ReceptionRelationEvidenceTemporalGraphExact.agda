module DASHI.Governance.ReceptionRelationEvidenceTemporalGraphExact where

------------------------------------------------------------------------
-- RECEPTION GRAPH: RELATION KIND x EVIDENCE STRENGTH x TEMPORAL PROVENANCE
--
-- Extends the merged suffrage/witch typed-genealogy discipline and the local
-- collective-memory reception carrier.  An edge records WHAT kind of reception
-- relation is claimed, HOW strong the evidence is, and WHERE in time/provenance
-- the evidence sits.  None of these axes rewrites another.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SuffrageWitchReclamationGenealogyExact as Genealogy
import DASHI.Governance.CollectiveMemoryReceptionHistoryExact as Reception

------------------------------------------------------------------------
-- 1. Generic graph vocabulary.
------------------------------------------------------------------------

data ReceptionNode : Set where
  sourceText
  firstReception
  institutionalVocabulary
  laterReinterpretation
  presentUseNode
  independentRediscoveryNode
  : ReceptionNode

data ReceptionRelationKind : Set where
  directCitation
  explicitReinterpretation
  lexicalBorrowing
  institutionalAdoption
  independentRediscovery
  contestedGenealogy
  archivalRecoveryRelation
  : ReceptionRelationKind

data ReceptionEvidenceStrength : Set where
  directPrimaryReceipt
  explicitSecondaryReceipt
  circumstantialReceipt
  contestedReceipt
  unsupportedReceipt
  : ReceptionEvidenceStrength

data TemporalProvenance : Set where
  contemporaneousWithSource
  nearContemporaryReception
  laterInstitutionalLayer
  retrospectiveReconstruction
  presentInterpretationLayer
  unresolvedTemporalLayer
  : TemporalProvenance

record ReceptionSourceReceipt : Set where
  constructor reception-source-receipt
  field
    authorOrInstitution : String
    title : String
    identifier : String
    sourceRole : String

open ReceptionSourceReceipt public

record ReceptionEdge : Set where
  constructor reception-edge
  field
    from : ReceptionNode
    to : ReceptionNode
    relationKind : ReceptionRelationKind
    evidenceStrength : ReceptionEvidenceStrength
    temporalProvenance : TemporalProvenance
    sourceReceipt : ReceptionSourceReceipt
    boundedReading : String

open ReceptionEdge public

------------------------------------------------------------------------
-- 2. Canonical finite examples of distinct edge kinds.
------------------------------------------------------------------------

sourcePrimary : ReceptionSourceReceipt
sourcePrimary = reception-source-receipt
  "source author"
  "source work"
  "finite DASHI source placeholder; no historical identifier asserted"
  "calibration receipt for direct citation structure only"

laterCommentary : ReceptionSourceReceipt
laterCommentary = reception-source-receipt
  "later interpreter"
  "later commentary"
  "finite DASHI commentary placeholder; no historical identifier asserted"
  "calibration receipt for reinterpretation structure only"

institutionalArchiveReceipt : ReceptionSourceReceipt
institutionalArchiveReceipt = reception-source-receipt
  "institutional archive"
  "terminology record"
  "finite DASHI archive placeholder; no historical identifier asserted"
  "calibration receipt for institutional-adoption structure only"

directCitationEdge : ReceptionEdge
directCitationEdge = reception-edge
  sourceText firstReception
  directCitation directPrimaryReceipt contemporaneousWithSource
  sourcePrimary
  "explicit source-to-reception citation edge"

reinterpretationEdge : ReceptionEdge
reinterpretationEdge = reception-edge
  firstReception laterReinterpretation
  explicitReinterpretation explicitSecondaryReceipt laterInstitutionalLayer
  laterCommentary
  "later source explicitly reinterprets the received proposition"

lexicalBorrowingEdge : ReceptionEdge
lexicalBorrowingEdge = reception-edge
  institutionalVocabulary presentUseNode
  lexicalBorrowing circumstantialReceipt presentInterpretationLayer
  institutionalArchiveReceipt
  "same vocabulary is observed without a direct source-citation receipt"

rediscoveryEdge : ReceptionEdge
rediscoveryEdge = reception-edge
  independentRediscoveryNode presentUseNode
  independentRediscovery explicitSecondaryReceipt presentInterpretationLayer
  laterCommentary
  "similar proposition is documented as independently reconstructed rather than transmitted"

contestedGenealogyEdge : ReceptionEdge
contestedGenealogyEdge = reception-edge
  sourceText presentUseNode
  contestedGenealogy contestedReceipt retrospectiveReconstruction
  laterCommentary
  "genealogical relation is proposed but remains contested"

------------------------------------------------------------------------
-- 3. Edge-kind distinctions are exact.
------------------------------------------------------------------------

directCitationNotLexicalBorrowing : directCitation ≡ lexicalBorrowing -> ⊥
directCitationNotLexicalBorrowing ()

reinterpretationNotIndependentRediscovery :
  explicitReinterpretation ≡ independentRediscovery -> ⊥
reinterpretationNotIndependentRediscovery ()

institutionalAdoptionNotDirectCitation : institutionalAdoption ≡ directCitation -> ⊥
institutionalAdoptionNotDirectCitation ()

contestedGenealogyNotDirectCitation : contestedGenealogy ≡ directCitation -> ⊥
contestedGenealogyNotDirectCitation ()

------------------------------------------------------------------------
-- 4. Evidence strength does not rewrite relation kind.
------------------------------------------------------------------------

record EdgePromotionReceipt (edge : ReceptionEdge) : Set where
  constructor edge-promotion-receipt
  field
    relationAppropriate : Bool
    sourceMatchesClaim : Bool
    temporalRouteLocated : Bool
    semanticComparisonPerformed : Bool
    promotionReading : String

open EdgePromotionReceipt public

data StrongEvidencePromotesDirectCitation : Set where

data SharedVocabularyPromotesLexicalTransmission : Set where

data SimilarMeaningPromotesGenealogy : Set where

data TemporalProximityPromotesInfluence : Set where

strongEvidenceDoesNotRewriteRelationKind :
  StrongEvidencePromotesDirectCitation -> ⊥
strongEvidenceDoesNotRewriteRelationKind ()

sharedVocabularyDoesNotPromoteTransmission :
  SharedVocabularyPromotesLexicalTransmission -> ⊥
sharedVocabularyDoesNotPromoteTransmission ()

similarMeaningDoesNotPromoteGenealogy : SimilarMeaningPromotesGenealogy -> ⊥
similarMeaningDoesNotPromoteGenealogy ()

temporalProximityDoesNotPromoteInfluence : TemporalProximityPromotesInfluence -> ⊥
temporalProximityDoesNotPromoteInfluence ()

------------------------------------------------------------------------
-- 5. Same present vocabulary can remain graph-ambiguous.
------------------------------------------------------------------------

data ReceptionPathFineState : Set where
  transmittedVocabularyPath
  independentlyRediscoveredPath
  : ReceptionPathFineState

presentVocabulary : ReceptionPathFineState -> String
presentVocabulary _ = "same present term"

pathRelation : ReceptionPathFineState -> ReceptionRelationKind
pathRelation transmittedVocabularyPath = lexicalBorrowing
pathRelation independentlyRediscoveredPath = independentRediscovery

presentVocabularyCannotRecoverReceptionPath :
  INF.FactorsThrough presentVocabulary pathRelation -> ⊥
presentVocabularyCannotRecoverReceptionPath =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      transmittedVocabularyPath
      independentlyRediscoveredPath
      refl
      (λ ()))

------------------------------------------------------------------------
-- 6. Small composable reception path.
------------------------------------------------------------------------

record ComposableReceptionPair : Set where
  constructor composable-reception-pair
  field
    firstEdge : ReceptionEdge
    secondEdge : ReceptionEdge
    commonNode : ReceptionNode
    firstEndsAtCommon : to firstEdge ≡ commonNode
    secondStartsAtCommon : from secondEdge ≡ commonNode

open ComposableReceptionPair public

citationThenReinterpretation : ComposableReceptionPair
citationThenReinterpretation =
  composable-reception-pair directCitationEdge reinterpretationEdge
    firstReception refl refl

------------------------------------------------------------------------
-- 7. Cross-pollination with existing merged/local boundaries.
------------------------------------------------------------------------

mergedGenealogyRelationAndEvidenceAxesRetained : Bool
mergedGenealogyRelationAndEvidenceAxesRetained = true

localVocabularyStillDoesNotRecoverMeaning :
  INF.FactorsThrough Reception.vocabularySurface Reception.semanticHistory -> ⊥
localVocabularyStillDoesNotRecoverMeaning =
  Reception.sameVocabularyCannotRecoverSemanticHistory

localVocabularyStillDoesNotRecoverInstitution :
  INF.FactorsThrough
    Reception.institutionalVocabularySurface
    Reception.institutionalHistory -> ⊥
localVocabularyStillDoesNotRecoverInstitution =
  Reception.sameVocabularyCannotRecoverInstitutionalHistory

------------------------------------------------------------------------
-- 8. Boundary.
------------------------------------------------------------------------

record ReceptionGraphBoundary : Set where
  constructor reception-graph-boundary
  field
    relationKindAndEvidenceStrengthIndependent : Bool
    temporalProvenanceIndependent : Bool
    directCitationEqualsLexicalBorrowing : Bool
    reinterpretationEqualsRediscovery : Bool
    strongEvidenceRewritesRelationKind : Bool
    samePresentVocabularyDeterminesPath : Bool
    semanticResemblanceProvesGenealogy : Bool
    graphCanRepresentContestedEdges : Bool

canonicalReceptionGraphBoundary : ReceptionGraphBoundary
canonicalReceptionGraphBoundary =
  reception-graph-boundary true true false false false false false true
