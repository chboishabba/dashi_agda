module DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire

------------------------------------------------------------------------
-- Exact observation/compiler ABI mirrored by
-- chboishabba/slr :: crates/sl-world-compiler.
--
-- Observation wire v1:
--   magic[4] = "SLRO"
--   version  = u16 little-endian 1
--   record kind 1 = source manifestation
--   record kind 2 = spaCy token/dependency observation
--
-- Token observations carry document identity, sentence/local ordinals,
-- source span, head ordinal, a numeric DependencyShape tag, orth/lemma and
-- head orth/lemma.  No JSON object and no regex-derived semantic field is an
-- executable input to the compiler.
------------------------------------------------------------------------

observationWireVersion : Nat
observationWireVersion = 1

data ObservationWireKind : Set where
  sourceManifestationObservation : ObservationWireKind
  tokenDependencyObservation : ObservationWireKind

observationWireKindTag : ObservationWireKind → Nat
observationWireKindTag sourceManifestationObservation = 1
observationWireKindTag tokenDependencyObservation = 2

dependencyShapeTag : Spacy.DependencyShape → Nat
dependencyShapeTag Spacy.nominalSubject = 1
dependencyShapeTag Spacy.directObject = 2
dependencyShapeTag Spacy.passiveSubject = 3
dependencyShapeTag Spacy.adjectivalModifier = 4
dependencyShapeTag Spacy.nominalModifier = 5
dependencyShapeTag Spacy.conjunction = 6
dependencyShapeTag Spacy.negation = 7
dependencyShapeTag Spacy.modalAuxiliary = 8
dependencyShapeTag Spacy.determiner = 9
dependencyShapeTag Spacy.temporalModifier = 10
dependencyShapeTag Spacy.clausalComplement = 11
dependencyShapeTag Spacy.openClausalComplement = 12
dependencyShapeTag Spacy.adverbialClause = 13
dependencyShapeTag Spacy.clausalModifier = 14
dependencyShapeTag Spacy.relativeClause = 15
dependencyShapeTag Spacy.unresolvedDependency = 16

data CompilerFragmentKind : Set where
  actorFragment : CompilerFragmentKind
  patientFragment : CompilerFragmentKind
  propertyFragment : CompilerFragmentKind
  relationFragment : CompilerFragmentKind
  conjunctionFragment : CompilerFragmentKind
  negationFragment : CompilerFragmentKind
  modalityFragment : CompilerFragmentKind
  quantifierFragment : CompilerFragmentKind
  temporalFragment : CompilerFragmentKind
  contentClauseFragment : CompilerFragmentKind
  clauseAttachmentFragment : CompilerFragmentKind
  unresolvedFragment : CompilerFragmentKind

compilerFragmentTag : CompilerFragmentKind → Nat
compilerFragmentTag actorFragment = 1
compilerFragmentTag patientFragment = 2
compilerFragmentTag propertyFragment = 3
compilerFragmentTag relationFragment = 4
compilerFragmentTag conjunctionFragment = 5
compilerFragmentTag negationFragment = 6
compilerFragmentTag modalityFragment = 7
compilerFragmentTag quantifierFragment = 8
compilerFragmentTag temporalFragment = 9
compilerFragmentTag contentClauseFragment = 10
compilerFragmentTag clauseAttachmentFragment = 11
compilerFragmentTag unresolvedFragment = 12

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

compileFragmentForShape : Spacy.DependencyShape → Maybe CompilerFragmentKind
compileFragmentForShape Spacy.nominalSubject = just actorFragment
compileFragmentForShape Spacy.directObject = just patientFragment
compileFragmentForShape Spacy.passiveSubject = just actorFragment
compileFragmentForShape Spacy.adjectivalModifier = just propertyFragment
compileFragmentForShape Spacy.nominalModifier = just propertyFragment
compileFragmentForShape Spacy.conjunction = just conjunctionFragment
compileFragmentForShape Spacy.negation = just negationFragment
compileFragmentForShape Spacy.modalAuxiliary = just modalityFragment
compileFragmentForShape Spacy.determiner = nothing
compileFragmentForShape Spacy.temporalModifier = just temporalFragment
compileFragmentForShape Spacy.clausalComplement = just contentClauseFragment
compileFragmentForShape Spacy.openClausalComplement = just contentClauseFragment
compileFragmentForShape Spacy.adverbialClause = just clauseAttachmentFragment
compileFragmentForShape Spacy.clausalModifier = just clauseAttachmentFragment
compileFragmentForShape Spacy.relativeClause = just clauseAttachmentFragment
compileFragmentForShape Spacy.unresolvedDependency = nothing

record ObservationCompilerParity : Set where
  constructor observationCompilerParity
  field
    magicIsSLRO : Bool
    versionIsOne : Bool
    littleEndianNumericFields : Bool
    dependencyTagMappingExact : Bool
    fragmentMappingExact : Bool
    documentRefRetained : Bool
    sentenceAndLocalOrdinalRetained : Bool
    sourceSpanRetained : Bool
    headOrdinalRetained : Bool
    dependentOrthLemmaRetained : Bool
    headOrthLemmaRetained : Bool
    observationDecodedIncrementally : Bool
    compilerEmitsSLRW : Bool
    compilerEmitsManifestationBeforeSemanticCandidates : Bool
    compilerCandidatesAreCandidateOnly : Bool
    unresolvedDependencyPromoted : Bool
    jsonTransportUsed : Bool
    regexSemanticParserUsed : Bool
    compilerCreatesSemanticAuthority : Bool
    semanticPromotion : Bool

open ObservationCompilerParity public

canonicalObservationCompilerParity : ObservationCompilerParity
canonicalObservationCompilerParity =
  observationCompilerParity
    true true true true true
    true true true true true true
    true true true true
    false false false false false

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data JsonObservationTransport : Set where
data RegexObservationSemanticParser : Set where
data UnresolvedDependencyPromotion : Set where
data CompilerSemanticAuthority : Set where
data CompilerTruthPromotion : Set where

jsonObservationTransportForbidden : JsonObservationTransport → ⊥
jsonObservationTransportForbidden ()

regexObservationSemanticParserForbidden : RegexObservationSemanticParser → ⊥
regexObservationSemanticParserForbidden ()

unresolvedDependencyCannotPromote : UnresolvedDependencyPromotion → ⊥
unresolvedDependencyCannotPromote ()

compilerDoesNotCreateSemanticAuthority : CompilerSemanticAuthority → ⊥
compilerDoesNotCreateSemanticAuthority ()

compilerDoesNotPromoteTruth : CompilerTruthPromotion → ⊥
compilerDoesNotPromoteTruth ()

-- The world-store output remains the exact SLRW ABI already formalised.
compilerTargetsWorldWireVersion : Nat
compilerTargetsWorldWireVersion = WorldWire.wireVersion
