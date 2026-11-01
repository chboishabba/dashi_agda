module DASHI.Ontology.WikidataBFOApplicabilityFibreExact where

------------------------------------------------------------------------
-- BFO APPLICABILITY AS A FIBRE OVER THE BROADER WIKIDATA CARRIER
--
-- Q35120 is used as the broad Wikidata-root-facing entity carrier, while
-- Q136433660 is the BFO Entity-facing root.  The operationally useful model is
-- therefore not identity of the two roots but a BFO applicability fibre over
-- the broader Wikidata carrier.
--
-- This file deliberately does NOT settle whether fictional characters,
-- mathematical objects, imagined things, etc. are BFO entities.  Instead it
-- formalises the epistemic shape required to ask such questions without
-- collapsing:
--
--   supported yes
--   supported no
--   not established
--   outside the currently committed BFO scope
--   conflicting derivations
--
-- The same referent and provenance are retained while the inspection question
-- moves from Wikidata membership to BFO Entity to a specific BFO partition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Level

------------------------------------------------------------------------
-- Inspection layers and non-binary evaluation states.
------------------------------------------------------------------------

data OntologyInspectionLevel : Set where
  wikidataEntityLevel : OntologyInspectionLevel
  bfoEntityLevel : OntologyInspectionLevel
  bfoContinuantOccurrentLevel : OntologyInspectionLevel

data ClaimEvaluation : Set where
  supportedYes : ClaimEvaluation
  supportedNo : ClaimEvaluation
  notEstablished : ClaimEvaluation
  outsideCommittedScope : ClaimEvaluation
  conflictingDerivations : ClaimEvaluation

supportedNoDiffersFromNotEstablished :
  supportedNo ≡ notEstablished → ⊥
supportedNoDiffersFromNotEstablished ()

notEstablishedDiffersFromOutsideScope :
  notEstablished ≡ outsideCommittedScope → ⊥
notEstablishedDiffersFromOutsideScope ()

outsideScopeDiffersFromConflict :
  outsideCommittedScope ≡ conflictingDerivations → ⊥
outsideScopeDiffersFromConflict ()

------------------------------------------------------------------------
-- Same referent/provenance may be inspected at several ontology levels.
------------------------------------------------------------------------

record ReferentInspection : Set where
  constructor referentInspection
  field
    referent : String
    level : OntologyInspectionLevel
    evaluation : ClaimEvaluation
    provenance : String

open ReferentInspection public

frodoWikidataInspection : ReferentInspection
frodoWikidataInspection =
  referentInspection
    "Frodo"
    wikidataEntityLevel
    supportedYes
    "illustrative referent; Wikidata-level membership question"

frodoBFOEntityInspection : ReferentInspection
frodoBFOEntityInspection =
  referentInspection
    "Frodo"
    bfoEntityLevel
    notEstablished
    "same illustrative referent; BFO Entity interpretation left open"

frodoBFOPartitionInspection : ReferentInspection
frodoBFOPartitionInspection =
  referentInspection
    "Frodo"
    bfoContinuantOccurrentLevel
    outsideCommittedScope
    "same illustrative referent; no partition classification asserted here"

frodoReferentPreservedAcrossLevels₀₁ :
  referent frodoWikidataInspection ≡ referent frodoBFOEntityInspection
frodoReferentPreservedAcrossLevels₀₁ = refl

frodoReferentPreservedAcrossLevels₁₂ :
  referent frodoBFOEntityInspection ≡ referent frodoBFOPartitionInspection
frodoReferentPreservedAcrossLevels₁₂ = refl

------------------------------------------------------------------------
-- A local unanswered/out-of-scope result cannot be promoted to falsehood.
------------------------------------------------------------------------

record BinaryDecoder : Set where
  constructor binaryDecoder
  field
    isTrue : ClaimEvaluation → Bool
    isFalse : ClaimEvaluation → Bool

open BinaryDecoder public

safeEvaluationDecoder : BinaryDecoder
safeEvaluationDecoder = binaryDecoder truth falsehood
  where
    truth : ClaimEvaluation → Bool
    truth supportedYes = true
    truth supportedNo = false
    truth notEstablished = false
    truth outsideCommittedScope = false
    truth conflictingDerivations = true

    falsehood : ClaimEvaluation → Bool
    falsehood supportedYes = false
    falsehood supportedNo = true
    falsehood notEstablished = false
    falsehood outsideCommittedScope = false
    falsehood conflictingDerivations = true

notEstablishedIsNeitherPositiveNorNegative :
  BinaryDecoder.isTrue safeEvaluationDecoder notEstablished ≡ false
  × BinaryDecoder.isFalse safeEvaluationDecoder notEstablished ≡ false
notEstablishedIsNeitherPositiveNorNegative = refl , refl

outsideScopeIsNeitherPositiveNorNegative :
  BinaryDecoder.isTrue safeEvaluationDecoder outsideCommittedScope ≡ false
  × BinaryDecoder.isFalse safeEvaluationDecoder outsideCommittedScope ≡ false
outsideScopeIsNeitherPositiveNorNegative = refl , refl

conflictCarriesBothPolarities :
  BinaryDecoder.isTrue safeEvaluationDecoder conflictingDerivations ≡ true
  × BinaryDecoder.isFalse safeEvaluationDecoder conflictingDerivations ≡ true
conflictCarriesBothPolarities = refl , refl

------------------------------------------------------------------------
-- Applicability transport: retain the whole referent while changing question.
------------------------------------------------------------------------

inspectionAsSituatedArgument :
  ReferentInspection →
  Level.SituatedArgument String OntologyInspectionLevel String
inspectionAsSituatedArgument inspection =
  Level.situatedArgument
    (referent inspection)
    (level inspection)
    (provenance inspection)

frodoLevelTransport₀₁ :
  Level.LevelTransport
    (inspectionAsSituatedArgument frodoWikidataInspection)
    (inspectionAsSituatedArgument frodoBFOEntityInspection)
frodoLevelTransport₀₁ = Level.levelTransport refl refl

frodoLevelTransport₁₂ :
  Level.LevelTransport
    (inspectionAsSituatedArgument frodoBFOEntityInspection)
    (inspectionAsSituatedArgument frodoBFOPartitionInspection)
frodoLevelTransport₁₂ = Level.levelTransport refl refl

frodoWholeTransport :
  Level.LevelTransport
    (inspectionAsSituatedArgument frodoWikidataInspection)
    (inspectionAsSituatedArgument frodoBFOPartitionInspection)
frodoWholeTransport = Level.composeLevelTransport frodoLevelTransport₀₁ frodoLevelTransport₁₂

------------------------------------------------------------------------
-- Boundary: the broad carrier and BFO applicability fibre must remain distinct.
------------------------------------------------------------------------

record BFOApplicabilityBoundary : Set where
  constructor bfoApplicabilityBoundary
  field
    wikidataEntityImpliesBFOEntity : Bool
    unknownBFOStatusMeansFalse : Bool
    outsideScopeMeansFalse : Bool
    conflictMeansUnknown : Bool
    sameReferentCanSurviveLevelChange : Bool
    provenanceSurvivesLevelChange : Bool
    bfoApplicabilityIsSeparateFromWikidataMembership : Bool

canonicalBFOApplicabilityBoundary : BFOApplicabilityBoundary
canonicalBFOApplicabilityBoundary =
  bfoApplicabilityBoundary false false false false true true true
