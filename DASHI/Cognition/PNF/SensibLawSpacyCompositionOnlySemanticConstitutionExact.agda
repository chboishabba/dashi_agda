module DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Reasoning.SpacyExecutableSemanticRuleBankExact as RuleBank
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Cognition.PNF.SensibLawRelationAttachmentCandidateProducerExact as Relation

------------------------------------------------------------------------
-- SENSIBLAW SPACY-COMPOSITION-ONLY SEMANTIC CONSTITUTION
--
-- Archaeology source:
--   * legacy Python ObligationAtom lane was a conceptual playground;
--   * useful ideas: clause locality, explicit source spans, role/scope separation;
--   * rejected mechanisms: regex cleanup, positional actor/action/object slicing,
--     phrase dictionaries as semantic authority, and lexical matcher promotion.
--
-- Current doctrine:
--   parser observation
--     -> syntactic projection
--     -> structural composition / accessibility
--     -> set-valued semantic candidates
--     -> contextual resolution
--     -> governed admission.
--
-- No regex/string-pattern oracle is a semantic input to this derivation path.
------------------------------------------------------------------------

data SemanticStage : Set where
  parserObservation : SemanticStage
  syntacticProjection : SemanticStage
  structuralComposition : SemanticStage
  semanticCandidateFibre : SemanticStage
  contextualResolution : SemanticStage
  governedAdmission : SemanticStage

infix 4 _↝_
data _↝_ : SemanticStage → SemanticStage → Set where
  parserToSyntax : parserObservation ↝ syntacticProjection
  syntaxToStructure : syntacticProjection ↝ structuralComposition
  structureToCandidates : structuralComposition ↝ semanticCandidateFibre
  candidatesToContext : semanticCandidateFibre ↝ contextualResolution
  contextToAdmission : contextualResolution ↝ governedAdmission

------------------------------------------------------------------------
-- Parser-supported structural carrier.
------------------------------------------------------------------------

data SyntacticRole : Set where
  subjectRole objectRole obliqueRole complementRole argumentRole : SyntacticRole

data AccessibilityPath : Set where
  sameClause : AccessibilityPath
  governingClause : AccessibilityPath
  precedingCoordinatedClause : AccessibilityPath
  sameSentence : AccessibilityPath
  precedingDiscourseUnit : AccessibilityPath
  reportingContentBoundary : AccessibilityPath
  precedingParagraph : AccessibilityPath
  precedingDocumentUnit : AccessibilityPath

record SyntacticProjectionReceipt : Set where
  constructor syntacticProjectionReceipt
  field
    row : Spacy.NumericTokenRow
    role : SyntacticRole
    declarationReference : String
    parserDependencyUsed : Bool
    parserHeadUsed : Bool
    sourceCoordinateRetained : Bool
    semanticRoleSelected : Bool

open SyntacticProjectionReceipt public

record StructuralCompositionReceipt : Set where
  constructor structuralCompositionReceipt
  field
    focus : SyntacticProjectionReceipt
    supportingRows : List Spacy.NumericTokenRow
    accessibility : List AccessibilityPath
    compositionReference : String
    parserOnlyInputs : Bool
    regexInputs : Bool
    lexicalSurfacePatternOracle : Bool

open StructuralCompositionReceipt public

------------------------------------------------------------------------
-- Set-valued semantics: structural composition may narrow a fibre but may not
-- manufacture a unique legal meaning merely from one dependency label.
------------------------------------------------------------------------

data CandidateRole : Set where
  actorCandidate : CandidateRole
  objectCandidate : CandidateRole
  jurisdictionCandidate : CandidateRole
  evidenceCandidate : CandidateRole
  provenanceCandidate : CandidateRole
  qualifierCandidate : CandidateRole
  conditionCandidate : CandidateRole
  exceptionCandidate : CandidateRole
  temporalCandidate : CandidateRole
  unresolvedRelationCandidate : CandidateRole

record SemanticCandidateFibre : Set where
  constructor semanticCandidateFibre
  field
    source : StructuralCompositionReceipt
    alternatives : List CandidateRole
    candidateOnly : Bool
    contextResolutionRequired : Bool

open SemanticCandidateFibre public

record ContextualSemanticResolution : Set where
  constructor contextualSemanticResolution
  field
    sourceFibre : SemanticCandidateFibre
    selectedCandidate : CandidateRole
    supportingParserRows : List Spacy.NumericTokenRow
    accessibilityWitnesses : List AccessibilityPath
    resolverReference : String
    policyReference : String
    parserAloneWasSufficient : Bool
    regexWasUsed : Bool

open ContextualSemanticResolution public

------------------------------------------------------------------------
-- Canonical boundary witnesses.
------------------------------------------------------------------------

canonicalSyntacticProjectionBoundary : SyntacticProjectionReceipt → Bool
canonicalSyntacticProjectionBoundary receipt = semanticRoleSelected receipt

canonicalStructuralCompositionBoundary : StructuralCompositionReceipt → Bool
canonicalStructuralCompositionBoundary receipt = regexInputs receipt

record CompositionOnlyBoundary : Set where
  constructor compositionOnlyBoundary
  field
    regexMayProduceSemanticEvidence : Bool
    regexMayProduceSemanticEvidenceIsFalse : regexMayProduceSemanticEvidence ≡ false
    tokenPositionBeforeModalDefinesActor : Bool
    tokenPositionBeforeModalDefinesActorIsFalse : tokenPositionBeforeModalDefinesActor ≡ false
    firstTokenAfterModalDefinesAction : Bool
    firstTokenAfterModalDefinesActionIsFalse : firstTokenAfterModalDefinesAction ≡ false
    prepositionTextBoundaryDefinesObject : Bool
    prepositionTextBoundaryDefinesObjectIsFalse : prepositionTextBoundaryDefinesObject ≡ false
    phraseDictionaryDefinesScope : Bool
    phraseDictionaryDefinesScopeIsFalse : phraseDictionaryDefinesScope ≡ false
    dependencyLabelMayNarrowSyntacticRole : Bool
    dependencyLabelMayNarrowSyntacticRoleIsTrue : dependencyLabelMayNarrowSyntacticRole ≡ true
    dependencyLabelAloneChoosesLegalRole : Bool
    dependencyLabelAloneChoosesLegalRoleIsFalse : dependencyLabelAloneChoosesLegalRole ≡ false
    structuralAccessibilityMayRefineCandidateSet : Bool
    structuralAccessibilityMayRefineCandidateSetIsTrue : structuralAccessibilityMayRefineCandidateSet ≡ true
    emptyCandidateSetProvesSemanticAbsence : Bool
    emptyCandidateSetProvesSemanticAbsenceIsFalse : emptyCandidateSetProvesSemanticAbsence ≡ false
    semanticResolutionRequiresContextReceipt : Bool
    semanticResolutionRequiresContextReceiptIsTrue : semanticResolutionRequiresContextReceipt ≡ true
    semanticResolutionAutomaticallyAuthorizesAdmission : Bool
    semanticResolutionAutomaticallyAuthorizesAdmissionIsFalse : semanticResolutionAutomaticallyAuthorizesAdmission ≡ false

canonicalCompositionOnlyBoundary : CompositionOnlyBoundary
canonicalCompositionOnlyBoundary =
  compositionOnlyBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Hard no-go types for legacy semantic shortcuts.
------------------------------------------------------------------------

data RegexDerivedSemanticEvidence : Set where
data PositionalActorShortcut : Set where
data FirstPostModalActionShortcut : Set where
data PrepositionCutoffObjectShortcut : Set where
data PhraseDictionaryScopeShortcut : Set where
data DependencyLabelAloneChoosesLegalRole : Set where
data EmptyCandidateSetClosesMeaning : Set where

data ParserObservationDirectlyAuthorizesAdmission : Set where

regexCannotBeSemanticEvidence : RegexDerivedSemanticEvidence → ⊥
regexCannotBeSemanticEvidence ()

positionBeforeModalCannotDefineActor : PositionalActorShortcut → ⊥
positionBeforeModalCannotDefineActor ()

firstPostModalTokenCannotDefineAction : FirstPostModalActionShortcut → ⊥
firstPostModalTokenCannotDefineAction ()

prepositionCutoffCannotDefineObject : PrepositionCutoffObjectShortcut → ⊥
prepositionCutoffCannotDefineObject ()

phraseDictionaryCannotDefineScope : PhraseDictionaryScopeShortcut → ⊥
phraseDictionaryCannotDefineScope ()

dependencyLabelCannotAloneChooseLegalRole : DependencyLabelAloneChoosesLegalRole → ⊥
dependencyLabelCannotAloneChooseLegalRole ()

emptyCandidateSetDoesNotCloseMeaning : EmptyCandidateSetClosesMeaning → ⊥
emptyCandidateSetDoesNotCloseMeaning ()

parserObservationDoesNotAuthorizeAdmission : ParserObservationDirectlyAuthorizesAdmission → ⊥
parserObservationDoesNotAuthorizeAdmission ()

------------------------------------------------------------------------
-- Existing owners remain authoritative for rule-shape and admission currency.
------------------------------------------------------------------------

existingRuleBankStillRequiresShapeAdmission :
  RuleBank.determinerEdgeUniquelyChoosesQuantifier
    RuleBank.canonicalExecutableSemanticRuleBoundary ≡ false
existingRuleBankStillRequiresShapeAdmission = refl

existingAdmissionStillBlocksParserAuthority :
  Admission.ParserCandidateAloneAuthorizesAdmission → ⊥
existingAdmissionStillBlocksParserAuthority =
  Admission.parserCandidateAloneCannotAuthorizeAdmission

existingRelationProducerStillRequiresContext :
  Relation.contextResolutionRequired
    (Relation.candidate Relation.canonicalRelationProducerBoundary) ≡ true
existingRelationProducerStillRequiresContext = refl
