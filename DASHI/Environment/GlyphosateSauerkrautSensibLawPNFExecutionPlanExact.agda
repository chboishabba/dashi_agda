module DASHI.Environment.GlyphosateSauerkrautSensibLawPNFExecutionPlanExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.SensibLawSpacyPredicateNormalFormBridgeExact as SpacyBridge
import DASHI.Reasoning.SensibLawCorpusWorldPNFBridgeExact as WorldBridge
import DASHI.Environment.GlyphosateSauerkrautAssertionPNFConeExact as Claim

------------------------------------------------------------------------
-- EXECUTION TARGET, NOT A FABRICATED PARSER RECEIPT
--
-- No Harle/Saga-of-Soggy-Sauerkraut artifact was found in the current
-- SensibLaw repository search. This module therefore specifies the exact
-- source/corpus/world run that should produce a concrete numeric-PNF receipt;
-- it does not claim that the spaCy run has already occurred.
------------------------------------------------------------------------

data ParserRunMaterialisation : Set where
  parserRunNotMaterialised
  parserRunMaterialised
  : ParserRunMaterialisation

notMaterialisedNotMaterialised :
  parserRunNotMaterialised ≡ parserRunMaterialised → ⊥
notMaterialisedNotMaterialised ()

record SensibLawPNFExecutionTarget : Set where
  constructor sensibLawPNFExecutionTarget
  field
    assertion : Cone.NaturalLanguageExperimentalAssertion
    canonicalText : String
    canonicalTextExact : canonicalText ≡ Cone.exactText assertion
    sourceDocumentReference : String
    sourceLocatorReference : String
    citedSourceReferences : List String
    externalWorldDemandReferences : List String
    parserContractReference : String
    numericPNFCompilerReference : String
    evidentialBridgeExporterReference : String
    evidentialBridgeSchemaReference : String
    expectedOutputReference : String
    materialisation : ParserRunMaterialisation
    materialisationReference : String

open SensibLawPNFExecutionTarget public

shioctonSensibLawExecutionTarget : SensibLawPNFExecutionTarget
shioctonSensibLawExecutionTarget = sensibLawPNFExecutionTarget
  Claim.shioctonNaturalAssertion
  Claim.shioctonExactResultText
  refl
  "Harle et al. 2024, Saga of Soggy Sauerkraut, HortScience 59(11), DOI 10.21273/HORTSCI18041-24"
  "Table 10 plus surrounding methods/design text"
  ( "paper references used for glyphosate/AMPA degradation mechanism claims"
  ∷ "paper references used for Lactiplantibacillus/LAB claims"
  ∷ "paper references used for assay and soil-process interpretation"
  ∷ [])
  ( "cross-document identity for cited microbial degradation claims"
  ∷ "external evidence for natural soil glyphosate/AMPA attenuation"
  ∷ "external evidence for assay interpretation and sorption/transformation distinctions"
  ∷ "transport evidence beyond Shiocton/Kidder sites"
  ∷ [])
  "SensibLaw streaming spaCy parser execution / PackedSentenceFibre authority path"
  "SensibLaw strict numeric-pnf-hyperfabric-compiler:v1"
  "SensibLaw PR #489 src/pnf/evidential_pnf_receipt.py"
  "sl.evidential_pnf_bridge.v0_1"
  "numeric PNF compilation -> sl.evidential_pnf_bridge.v0_1 -> SensibLawNumericPNFReceipt -> ParserToEvidencePNFCorrespondence -> document/source/world horizon receipts"
  parserRunNotMaterialised
  "current repository search found no already-ingested Harle/sauerkraut artifact; execute/import source before installing a concrete parser receipt"

------------------------------------------------------------------------
-- Concrete activation requires the actual SensiBlaw result.
------------------------------------------------------------------------

record MaterialisedGlyphosateSpacyPNF : Set₁ where
  constructor materialisedGlyphosateSpacyPNF
  field
    target : SensibLawPNFExecutionTarget
    targetIsShiocton : target ≡ shioctonSensibLawExecutionTarget
    numericReceipt :
      SpacyBridge.SensibLawNumericPNFReceipt Claim.shioctonNaturalAssertion
    corpusWorldContext :
      WorldBridge.SensibLawCorpusWorldContext numericReceipt
    bridgeReceiptArtifactReference : String
    runArtifactReference : String
    replayReference : String

open MaterialisedGlyphosateSpacyPNF public

record GlyphosateSensibLawExecutionBoundary : Set where
  constructor glyphosateSensibLawExecutionBoundary
  field
    executionPlanEqualsExecutedParserRun : Bool
    executionPlanEqualsExecutedParserRunIsFalse :
      executionPlanEqualsExecutedParserRun ≡ false
    concreteParserReceiptRequiresMaterialisedRun : Bool
    concreteParserReceiptRequiresMaterialisedRunIsTrue :
      concreteParserReceiptRequiresMaterialisedRun ≡ true
    runtimeExporterNowHasStableSchema : Bool
    runtimeExporterNowHasStableSchemaIsTrue :
      runtimeExporterNowHasStableSchema ≡ true
    exportedReceiptEqualsSemanticCorrespondence : Bool
    exportedReceiptEqualsSemanticCorrespondenceIsFalse :
      exportedReceiptEqualsSemanticCorrespondence ≡ false
    paperSourceAndWorldDemandsCanShareOneExecutionTarget : Bool
    paperSourceAndWorldDemandsCanShareOneExecutionTargetIsTrue :
      paperSourceAndWorldDemandsCanShareOneExecutionTarget ≡ true

canonicalGlyphosateSensibLawExecutionBoundary :
  GlyphosateSensibLawExecutionBoundary
canonicalGlyphosateSensibLawExecutionBoundary =
  glyphosateSensibLawExecutionBoundary
    false refl
    true refl
    true refl
    false refl
    true refl
