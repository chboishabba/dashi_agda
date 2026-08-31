module DASHI.Reasoning.SensibLawSpacyPredicateNormalFormBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.NumericPNFCompilation as NumericPNF
import DASHI.Cognition.PNF.ExactlyOnceParserAuthorityProjectionExact as ExactlyOnce
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as EvidencePNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- TWO PNF SENSES, ONE EXPLICIT BRIDGE
--
-- SensibLaw's numeric/parser PNF is a source-anchored computational carrier
-- built from spaCy observations, exactly-once sentence ownership, regional
-- closure and residual demands. DASHI's evidence-facing Predicate Normal Form
-- is a reviewed assertion object exposing quantifier, scope, predicates and
-- inferential force. The former supplies structured extraction evidence; it is
-- not definitionally the latter and cannot mint semantic/world authority.
------------------------------------------------------------------------

data PNFSense : Set where
  parserNumericPNF
  evidentialPredicateNormalForm
  : PNFSense

parserPNFNotEvidentialPNF :
  parserNumericPNF ≡ evidentialPredicateNormalForm → ⊥
parserPNFNotEvidentialPNF ()

record SensibLawNumericPNFReceipt
    (source : Cone.NaturalLanguageExperimentalAssertion) : Set₁ where
  constructor sensibLawNumericPNFReceipt
  field
    canonicalText : String
    canonicalTextMatchesSource :
      canonicalText ≡ Cone.exactText source

    runReference : String
    documentReference : String
    sentenceFibreReference : String
    parserContractReference : String
    numericPNFCompilerReference : String
    numericGraphReference : String
    residualDemandReferences : List String

    -- Existing formal boundaries consumed rather than duplicated.
    spacyBoundary : Spacy.SpacyProjectionBoundary
    spacyBoundaryCanonical :
      spacyBoundary ≡ Spacy.canonicalSpacyProjectionBoundary
    strictCompilerBoundary : NumericPNF.StrictCompilerBypassBoundary
    strictCompilerBoundaryCanonical :
      strictCompilerBoundary ≡ NumericPNF.canonicalStrictCompilerBypassBoundary

    exactlyOnceAuthorityReference : String
    boundaryCompletionReference : String
    parserObservationReference : String

open SensibLawNumericPNFReceipt public

------------------------------------------------------------------------
-- Semantic correspondence is a separate receipt.
--
-- Numeric parser factors/objects may help propose predicates, scope candidates
-- or dependency relations, but quantifier force, causal force and world-level
-- identity require an explicit reviewed interpretation. This matches the
-- SensibLaw runtime's own `world_resolution_deferred = true` boundary.
------------------------------------------------------------------------

record ParserToEvidencePNFCorrespondence
    {source : Cone.NaturalLanguageExperimentalAssertion}
    (parserReceipt : SensibLawNumericPNFReceipt source)
    (logicalReceipt : Cone.PNFCompilationReceipt source) : Set₁ where
  constructor parserToEvidencePNFCorrespondence
  field
    sameCanonicalText :
      canonicalText parserReceipt
      ≡ EvidencePNF.naturalLanguage (Cone.compiled logicalReceipt)

    tokenPredicateCorrespondenceReference : String
    dependencyRelationCorrespondenceReference : String
    scopeInterpretationReference : String
    quantifierInterpretationReference : String
    inferentialForceInterpretationReference : String
    unresolvedWorldDemandsReference : String
    humanOrIndependentReviewReference : String

open ParserToEvidencePNFCorrespondence public

parserTextReachesLogicalText :
  ∀ {source parserReceipt logicalReceipt} →
  ParserToEvidencePNFCorrespondence
    {source}
    parserReceipt
    logicalReceipt →
  canonicalText parserReceipt
  ≡ EvidencePNF.naturalLanguage (Cone.compiled logicalReceipt)
parserTextReachesLogicalText = sameCanonicalText

record SensibLawSpacyPNFBoundary : Set where
  constructor sensibLawSpacyPNFBoundary
  field
    parserObservationIsSemanticAuthority : Bool
    parserObservationIsSemanticAuthorityIsFalse :
      parserObservationIsSemanticAuthority ≡ false

    numericPNFEqualsEvidentialPNFByDefinition : Bool
    numericPNFEqualsEvidentialPNFByDefinitionIsFalse :
      numericPNFEqualsEvidentialPNFByDefinition ≡ false

    closedDocumentInterfaceClosesWorldResolution : Bool
    closedDocumentInterfaceClosesWorldResolutionIsFalse :
      closedDocumentInterfaceClosesWorldResolution ≡ false

    parserCanSupplyStructuredEvidenceForPNFCompilation : Bool
    parserCanSupplyStructuredEvidenceForPNFCompilationIsTrue :
      parserCanSupplyStructuredEvidenceForPNFCompilation ≡ true

    semanticCorrespondenceRequiresSeparateReceipt : Bool
    semanticCorrespondenceRequiresSeparateReceiptIsTrue :
      semanticCorrespondenceRequiresSeparateReceipt ≡ true

canonicalSensibLawSpacyPNFBoundary : SensibLawSpacyPNFBoundary
canonicalSensibLawSpacyPNFBoundary =
  sensibLawSpacyPNFBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
