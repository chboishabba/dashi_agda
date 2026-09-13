module DASHI.Culture.LinguisticMorphologySourceObservationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy

------------------------------------------------------------------------
-- LINGUISTIC MORPHOLOGY SOURCE / OBSERVATION BRIDGE
--
-- Source anchor:
-- Rochelle Lieber, "What is morphology?", Introducing Morphology,
-- Cambridge University Press, 2009/online 2012.
-- DOI: 10.1017/CBO9780511808845.004
--
-- Source scope: morphology as the study of word formation, including words and
-- morphemes, lexemes/word forms, inflection and derivation.  This module does
-- not attribute DASHI's receipt architecture to Lieber and does not promote a
-- parser annotation into linguistic truth.
------------------------------------------------------------------------

lieberMorphologySource : Attribution.AttributedSource
lieberMorphologySource = Attribution.mkDOISource
  "Rochelle Lieber"
  "What is morphology?"
  "Introducing Morphology, Cambridge University Press"
  "2009"
  "10.1017/CBO9780511808845.004"
  "https://doi.org/10.1017/CBO9780511808845.004"
  Attribution.academicChapterSource
  "source anchor for linguistic morphology vocabulary/scope; not an empirical analysis of a DASHI language corpus"
  Attribution.publicAttribution

lieberSourceRoleReceipt : AttributionSnowball.SourceRoleSnowballReceipt lieberMorphologySource
lieberSourceRoleReceipt = AttributionSnowball.canonicalSourceRoleSnowballReceipt lieberMorphologySource

data MorphologicalProcess : Set where
  inflection derivation compounding reduplication conversion otherProcess : MorphologicalProcess

data MorphemeRelation : Set where
  freeMorpheme boundMorpheme root stem affix unresolvedRelation : MorphemeRelation

record MorphologicalFormObservation : Set where
  constructor morphological-form-observation
  field
    languageOrVariety : String
    corpusReference : String
    corpusRevision : String
    tokenReference : String
    surfaceForm : String
    lemmaReference : String
    morphemeSegmentationReference : String
    rootStemReference : String
    process : MorphologicalProcess
    relation : MorphemeRelation
    grammaticalFeaturesReference : String
    parserObservationReference : String
    humanOrSourceAnalysisReference : String
    analysisRevision : String
open MorphologicalFormObservation public

record MorphologicalContrastReceipt : Set where
  constructor morphological-contrast-receipt
  field
    languageOrVariety : String
    formAReference : String
    formBReference : String
    sharedLexemeOrRootReference : String
    featureDifferenceReference : String
    distributionReference : String
    meaningOrGrammaticalDifferenceReference : String
    sourceEvidenceReference : String
    sameLanguageContext : Bool
    analysisPaid : Bool
open MorphologicalContrastReceipt public

------------------------------------------------------------------------
-- Existing parser reuse is observation-only.
------------------------------------------------------------------------

spacyMorphologyCapabilityKnown : Bool
spacyMorphologyCapabilityKnown = true

spacyBoundaryRetained : Spacy.SpacyProjectionBoundary
spacyBoundaryRetained = Spacy.canonicalSpacyProjectionBoundary

record LinguisticMorphologyFrontier : Set where
  constructor linguistic-morphology-frontier
  field
    attributedSourceLanePaid : Bool
    canonicalArchitecturePaid : Bool
    parserObservationSubstratePresent : Bool
    formObservationReceiptShapePaid : Bool
    contrastReceiptShapePaid : Bool
    concreteLanguageAnalysisPaid : Bool
    concreteCorpusProducerPaid : Bool
    architectureStillMissing : Bool
open LinguisticMorphologyFrontier public

currentLinguisticMorphologyFrontier : LinguisticMorphologyFrontier
currentLinguisticMorphologyFrontier =
  linguistic-morphology-frontier true true true true true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParserMorphTagCreatesMorphemeAnalysis : Set where
data OrthographicSubstringCreatesMorpheme : Set where
data WordFormationPatternTransfersAcrossLanguages : Set where
data SourceChapterCreatesCorpusEvidence : Set where
data MorphologyEqualsSyntax : Set where

parserTagDoesNotCreateMorphemeAnalysis : ParserMorphTagCreatesMorphemeAnalysis → ⊥
parserTagDoesNotCreateMorphemeAnalysis ()

substringDoesNotCreateMorpheme : OrthographicSubstringCreatesMorpheme → ⊥
substringDoesNotCreateMorpheme ()

patternDoesNotTransferWithoutLanguageEvidence : WordFormationPatternTransfersAcrossLanguages → ⊥
patternDoesNotTransferWithoutLanguageEvidence ()

sourceChapterIsNotCorpusEvidence : SourceChapterCreatesCorpusEvidence → ⊥
sourceChapterIsNotCorpusEvidence ()

morphologyDoesNotCollapseIntoSyntax : MorphologyEqualsSyntax → ⊥
morphologyDoesNotCollapseIntoSyntax ()

record LinguisticMorphologyBoundary : Set where
  constructor linguistic-morphology-boundary
  field
    sourceAttributionRetained : Bool
    wordMorphemeLexemeDistinctionsRetained : Bool
    inflectionDerivationSeparated : Bool
    parserIsObservationProducerOnly : Bool
    languageSpecificEvidenceStillRequired : Bool
    morphologyEqualsParserMorphTag : Bool
    morphologyEqualsSyntax : Bool
open LinguisticMorphologyBoundary public

canonicalLinguisticMorphologyBoundary : LinguisticMorphologyBoundary
canonicalLinguisticMorphologyBoundary =
  linguistic-morphology-boundary true true true true true false false
