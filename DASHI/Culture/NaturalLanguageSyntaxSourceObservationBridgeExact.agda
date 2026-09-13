module DASHI.Culture.NaturalLanguageSyntaxSourceObservationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy

------------------------------------------------------------------------
-- NATURAL-LANGUAGE SYNTAX SOURCE / OBSERVATION BRIDGE
--
-- Source anchors:
-- * Robert D. Van Valin Jr., "Dependency relations", An Introduction to Syntax,
--   Cambridge University Press. DOI: 10.1017/CBO9781139164320.004
-- * Andrew Carnie, Constituent Structure, Oxford University Press.
--   Book DOI: 10.1093/oso/9780199261994.001.0001
--   Chapter "Dependency and Constituency":
--   DOI: 10.1093/oso/9780199261994.003.0009
--
-- This owner deliberately preserves dependency and constituency as distinct
-- representation families. spaCy dependency arcs are parser observations, not
-- a definition of syntax and not a proof that one syntactic analysis is true.
------------------------------------------------------------------------

vanValinDependencySource : Attribution.AttributedSource
vanValinDependencySource = Attribution.mkDOISource
  "Robert D. Van Valin Jr."
  "Dependency relations"
  "An Introduction to Syntax, Cambridge University Press"
  "2001"
  "10.1017/CBO9781139164320.004"
  "https://doi.org/10.1017/CBO9781139164320.004"
  Attribution.academicChapterSource
  "source anchor for dependency relations and morphosyntactic co-occurrence; not authority over a DASHI parse"
  Attribution.publicAttribution

carnieConstituentSource : Attribution.AttributedSource
carnieConstituentSource = Attribution.mkDOISource
  "Andrew Carnie"
  "Dependency and Constituency"
  "Constituent Structure, Oxford University Press"
  "2007"
  "10.1093/oso/9780199261994.003.0009"
  "https://doi.org/10.1093/oso/9780199261994.003.0009"
  Attribution.academicChapterSource
  "source anchor for the relation between constituent and dependency representations; not authority over a DASHI parse"
  Attribution.publicAttribution

vanValinSourceRoleReceipt : AttributionSnowball.SourceRoleSnowballReceipt vanValinDependencySource
vanValinSourceRoleReceipt = AttributionSnowball.canonicalSourceRoleSnowballReceipt vanValinDependencySource

carnieSourceRoleReceipt : AttributionSnowball.SourceRoleSnowballReceipt carnieConstituentSource
carnieSourceRoleReceipt = AttributionSnowball.canonicalSourceRoleSnowballReceipt carnieConstituentSource

data SyntaxRepresentationFamily : Set where
  dependencyRepresentation constituencyRepresentation mixedRepresentation unresolvedRepresentation : SyntaxRepresentationFamily

data SyntacticRelationKind : Set where
  headDependent subjectPredicate argumentRelation modifierRelation coordinationRelation constituentDominance linearOrder otherSyntacticRelation : SyntacticRelationKind

record SyntacticUnitObservation : Set where
  constructor syntactic-unit-observation
  field
    languageOrVariety : String
    corpusReference : String
    corpusRevision : String
    sentenceReference : String
    tokenOrSpanReference : String
    surfaceTextReference : String
    lexicalCategoryReference : String
    morphologyReference : String
    parserObservationReference : String
    humanOrSourceAnalysisReference : String
    analysisRevision : String
open SyntacticUnitObservation public

record DependencyArcReceipt : Set where
  constructor dependency-arc-receipt
  field
    sentenceReference : String
    headReference : String
    dependentReference : String
    relationKind : SyntacticRelationKind
    parserRelationReference : String
    sourceOrHumanValidationReference : String
    sameSentencePaid : Bool
    dependencyAnalysisPaid : Bool
open DependencyArcReceipt public

record ConstituentReceipt : Set where
  constructor constituent-receipt
  field
    sentenceReference : String
    spanReference : String
    categoryReference : String
    childStructureReference : String
    constituencyEvidenceReference : String
    sourceOrHumanValidationReference : String
    sameSentencePaid : Bool
    constituencyAnalysisPaid : Bool
open ConstituentReceipt public

record SyntaxAnalysisReceipt : Set where
  constructor syntax-analysis-receipt
  field
    languageOrVariety : String
    sentenceReference : String
    representationFamily : SyntaxRepresentationFamily
    dependencyLedgerReference : String
    constituentLedgerReference : String
    linearOrderReference : String
    argumentStructureReference : String
    ambiguityLedgerReference : String
    sourceProvenanceReference : String
    analysisRevision : String
    alternateAnalysesRetained : Bool
    empiricalPromotionAllowed : Bool
open SyntaxAnalysisReceipt public

------------------------------------------------------------------------
-- Existing parser reuse remains observation-only.
------------------------------------------------------------------------

spacyDependencyCapabilityKnown : Bool
spacyDependencyCapabilityKnown = true

spacyBoundaryRetained : Spacy.SpacyProjectionBoundary
spacyBoundaryRetained = Spacy.canonicalSpacyProjectionBoundary

record NaturalLanguageSyntaxFrontier : Set where
  constructor natural-language-syntax-frontier
  field
    attributedDependencySourcePaid : Bool
    attributedConstituencySourcePaid : Bool
    dependencyReceiptShapePaid : Bool
    constituentReceiptShapePaid : Bool
    mixedAnalysisReceiptShapePaid : Bool
    parserObservationSubstratePresent : Bool
    concreteLanguageSyntaxAnalysisPaid : Bool
    architectureStillMissing : Bool
open NaturalLanguageSyntaxFrontier public

currentNaturalLanguageSyntaxFrontier : NaturalLanguageSyntaxFrontier
currentNaturalLanguageSyntaxFrontier =
  natural-language-syntax-frontier true true true true true true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParserDependencyCreatesSyntacticTruth : Set where
data DependencyEqualsConstituency : Set where
data ProgrammingSyntaxCreatesNaturalLanguageSyntax : Set where
data GrammaticalityCreatesSingleParse : Set where
data SurfaceOrderCreatesHierarchy : Set where
data SourceChapterCreatesCorpusParse : Set where

parserDependencyDoesNotCreateTruth : ParserDependencyCreatesSyntacticTruth → ⊥
parserDependencyDoesNotCreateTruth ()

dependencyDoesNotEqualConstituency : DependencyEqualsConstituency → ⊥
dependencyDoesNotEqualConstituency ()

programmingSyntaxIsNotNaturalLanguageSyntax : ProgrammingSyntaxCreatesNaturalLanguageSyntax → ⊥
programmingSyntaxIsNotNaturalLanguageSyntax ()

grammaticalityDoesNotCreateUniqueParse : GrammaticalityCreatesSingleParse → ⊥
grammaticalityDoesNotCreateUniqueParse ()

surfaceOrderDoesNotCreateHierarchy : SurfaceOrderCreatesHierarchy → ⊥
surfaceOrderDoesNotCreateHierarchy ()

sourceChapterIsNotCorpusParse : SourceChapterCreatesCorpusParse → ⊥
sourceChapterIsNotCorpusParse ()

record NaturalLanguageSyntaxBoundary : Set where
  constructor natural-language-syntax-boundary
  field
    dependencyAndConstituencyDistinct : Bool
    parserIsObservationProducerOnly : Bool
    sentenceIdentityExplicit : Bool
    ambiguityMayBeRetained : Bool
    languageSpecificEvidenceStillRequired : Bool
    parserDependencyEqualsSyntacticTruth : Bool
    programmingSyntaxEqualsNaturalLanguageSyntax : Bool
open NaturalLanguageSyntaxBoundary public

canonicalNaturalLanguageSyntaxBoundary : NaturalLanguageSyntaxBoundary
canonicalNaturalLanguageSyntaxBoundary =
  natural-language-syntax-boundary true true true true true false false
