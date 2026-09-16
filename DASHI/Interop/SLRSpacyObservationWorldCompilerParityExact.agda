module DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Spacy
import DASHI.Interop.SLRBinaryWorldWireParityExact as WorldWire

------------------------------------------------------------------------
-- Exact observation/compiler ABI mirrored by
-- chboishabba/slr :: crates/sl-world-compiler and the trained-spaCy binary
-- observation boundary in slr_spacy_observation_wire.py.
------------------------------------------------------------------------

observationWireVersion : Nat
observationWireVersion = 1

data ObservationWireKind : Set where
  sourceManifestationObservation : ObservationWireKind
  tokenDependencyObservation : ObservationWireKind

observationWireKindTag : ObservationWireKind → Nat
observationWireKindTag sourceManifestationObservation = 1
observationWireKindTag tokenDependencyObservation = 2

------------------------------------------------------------------------
-- The Python boundary recognizes only these exact dependency-label classes.
-- Unknown labels are retained as unresolvedDependency; they are not guessed.
------------------------------------------------------------------------

data SpacyDependencyLabel : Set where
  nsubjLabel csubjLabel : SpacyDependencyLabel
  objLabel dobjLabel iobjLabel pobjLabel : SpacyDependencyLabel
  nsubjpassLabel nsubjColonPassLabel csubjpassLabel csubjColonPassLabel : SpacyDependencyLabel
  amodLabel nmodLabel oblLabel : SpacyDependencyLabel
  conjLabel ccLabel negLabel : SpacyDependencyLabel
  auxLabel auxpassLabel auxColonPassLabel copLabel : SpacyDependencyLabel
  detLabel npadvmodLabel tmodLabel : SpacyDependencyLabel
  ccompLabel xcompLabel advclLabel aclLabel relclLabel aclColonRelclLabel : SpacyDependencyLabel
  unknownLabel : SpacyDependencyLabel

shapeForDependencyLabel : SpacyDependencyLabel → Spacy.DependencyShape
shapeForDependencyLabel nsubjLabel = Spacy.nominalSubject
shapeForDependencyLabel csubjLabel = Spacy.nominalSubject
shapeForDependencyLabel objLabel = Spacy.directObject
shapeForDependencyLabel dobjLabel = Spacy.directObject
shapeForDependencyLabel iobjLabel = Spacy.directObject
shapeForDependencyLabel pobjLabel = Spacy.directObject
shapeForDependencyLabel nsubjpassLabel = Spacy.passiveSubject
shapeForDependencyLabel nsubjColonPassLabel = Spacy.passiveSubject
shapeForDependencyLabel csubjpassLabel = Spacy.passiveSubject
shapeForDependencyLabel csubjColonPassLabel = Spacy.passiveSubject
shapeForDependencyLabel amodLabel = Spacy.adjectivalModifier
shapeForDependencyLabel nmodLabel = Spacy.nominalModifier
shapeForDependencyLabel oblLabel = Spacy.nominalModifier
shapeForDependencyLabel conjLabel = Spacy.conjunction
shapeForDependencyLabel ccLabel = Spacy.conjunction
shapeForDependencyLabel negLabel = Spacy.negation
shapeForDependencyLabel auxLabel = Spacy.modalAuxiliary
shapeForDependencyLabel auxpassLabel = Spacy.modalAuxiliary
shapeForDependencyLabel auxColonPassLabel = Spacy.modalAuxiliary
shapeForDependencyLabel copLabel = Spacy.modalAuxiliary
shapeForDependencyLabel detLabel = Spacy.determiner
shapeForDependencyLabel npadvmodLabel = Spacy.temporalModifier
shapeForDependencyLabel tmodLabel = Spacy.temporalModifier
shapeForDependencyLabel ccompLabel = Spacy.clausalComplement
shapeForDependencyLabel xcompLabel = Spacy.openClausalComplement
shapeForDependencyLabel advclLabel = Spacy.adverbialClause
shapeForDependencyLabel aclLabel = Spacy.clausalModifier
shapeForDependencyLabel relclLabel = Spacy.relativeClause
shapeForDependencyLabel aclColonRelclLabel = Spacy.relativeClause
shapeForDependencyLabel unknownLabel = Spacy.unresolvedDependency

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
  actorFragment patientFragment propertyFragment relationFragment : CompilerFragmentKind
  conjunctionFragment negationFragment modalityFragment quantifierFragment : CompilerFragmentKind
  temporalFragment contentClauseFragment clauseAttachmentFragment unresolvedFragment : CompilerFragmentKind

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
    dependencyLabelProjectionExact : Bool
    unknownDependencyRemainsUnresolved : Bool
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
    true true true true true true true
    true true true true true true
    true true true true
    false false false false false

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data JsonObservationTransport : Set where
data RegexObservationSemanticParser : Set where
data UnknownDependencyGuessing : Set where
data UnresolvedDependencyPromotion : Set where
data CompilerSemanticAuthority : Set where
data CompilerTruthPromotion : Set where

jsonObservationTransportForbidden : JsonObservationTransport → ⊥
jsonObservationTransportForbidden ()

regexObservationSemanticParserForbidden : RegexObservationSemanticParser → ⊥
regexObservationSemanticParserForbidden ()

unknownDependencyCannotBeGuessed : UnknownDependencyGuessing → ⊥
unknownDependencyCannotBeGuessed ()

unresolvedDependencyCannotPromote : UnresolvedDependencyPromotion → ⊥
unresolvedDependencyCannotPromote ()

compilerDoesNotCreateSemanticAuthority : CompilerSemanticAuthority → ⊥
compilerDoesNotCreateSemanticAuthority ()

compilerDoesNotPromoteTruth : CompilerTruthPromotion → ⊥
compilerDoesNotPromoteTruth ()

compilerTargetsWorldWireVersion : Nat
compilerTargetsWorldWireVersion = WorldWire.wireVersion
