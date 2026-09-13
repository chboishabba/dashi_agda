module DASHI.Interop.TiRCorderTlureyPrivateLexemeRuntimeParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Interop.TiRCorderVoiceEditInteroceptionAntiPanopticonExact as Voice
import DASHI.Interop.TiRCorderHumourTlureyContextIndexedGrammarExact as Grammar
import DASHI.Cognition.TlureyNumerologyStateSpace as Tlurey

------------------------------------------------------------------------
-- RUNTIME PARITY: TLUREY PRIVATE LEXEME -> TIRCORDER VOICE GRAMMAR
--
-- Mirrors tircorder/voice_grammar.py and tircorder/voice_intent.py.
-- The Python lane is executable; this owner records the intended typed seam.
------------------------------------------------------------------------

data RuntimeGrammarNamespace : Set where
  dictationNamespace : RuntimeGrammarNamespace
  editingNamespace : RuntimeGrammarNamespace
  codingNamespace : RuntimeGrammarNamespace
  shellNamespace : RuntimeGrammarNamespace
  navigationNamespace : RuntimeGrammarNamespace
  personalNamespace : RuntimeGrammarNamespace

record RuntimeSharedAnchorReceipt : Set where
  constructor runtimeSharedAnchorReceipt
  field
    anchorId : String
    namespace : RuntimeGrammarNamespace
    contextReference : String
    active : Bool

open RuntimeSharedAnchorReceipt public

record RuntimePrivateLexemeRule : Set where
  constructor runtimePrivateLexemeRule
  field
    ruleId : String
    lexeme : Tlurey.TlureyLexeme
    namespace : RuntimeGrammarNamespace
    outputFibre : Voice.SpokenIntentFibre
    outputKind : Voice.VoiceEditKind
    argumentReference : String
    requiresSharedAnchor : Bool
    sourceProvenanceReference : String

open RuntimePrivateLexemeRule public

record RuntimeGrammarBranch : Set where
  constructor runtimeGrammarBranch
  field
    rule : RuntimePrivateLexemeRule
    matchedSurfaceReference : String
    namespaceSatisfied : Bool
    contextSatisfied : Bool
    anchorSatisfied : Bool
    candidateScore : Nat
    rationaleReference : String

open RuntimeGrammarBranch public

record RuntimeLookupReceipt : Set where
  constructor runtimeLookupReceipt
  field
    utteranceReference : String
    namespace : RuntimeGrammarNamespace
    candidateCount : Nat
    literalContentCandidateRetained : Bool
    residualRuleReference : String
    residualRetained : Bool

open RuntimeLookupReceipt public

------------------------------------------------------------------------
-- Canonical private shorthand fixture.
------------------------------------------------------------------------

slapLexeme : Tlurey.TlureyLexeme
slapLexeme =
  Tlurey.tlureyLexeme
    "slap"
    "insert equals operator"
    "python-editing"
    true

slapCodingRule : RuntimePrivateLexemeRule
slapCodingRule =
  runtimePrivateLexemeRule
    "personal:slap"
    slapLexeme
    codingNamespace
    Voice.formattingCommand
    Voice.insertText
    "="
    true
    "user-registered private shorthand"

slapWithoutAnchor : RuntimeGrammarBranch
slapWithoutAnchor =
  runtimeGrammarBranch
    slapCodingRule
    "slap"
    true
    true
    false
    60
    "surface matched but required shared anchor is absent; branch retained non-executing"

slapWithMatchingAnchor : RuntimeGrammarBranch
slapWithMatchingAnchor =
  runtimeGrammarBranch
    slapCodingRule
    "slap"
    true
    true
    true
    100
    "surface, coding namespace, python-editing context and shared anchor all match"

------------------------------------------------------------------------
-- Admission and residual firewalls.
------------------------------------------------------------------------

data RuntimeCommandAdmission : RuntimeGrammarBranch → Set where
  admitAnchoredBranch :
    {branch : RuntimeGrammarBranch} →
    namespaceSatisfied branch ≡ true →
    contextSatisfied branch ≡ true →
    anchorSatisfied branch ≡ true →
    RuntimeCommandAdmission branch

slapWithoutAnchorCannotAdmit : RuntimeCommandAdmission slapWithoutAnchor → ⊥
slapWithoutAnchorCannotAdmit ()

slapWithAnchorCanAdmit : RuntimeCommandAdmission slapWithMatchingAnchor
slapWithAnchorCanAdmit = admitAnchoredBranch refl refl refl

data SurfaceMatchErasesLiteralContentCandidate : Set where
surfaceMatchDoesNotEraseLiteralContentCandidate :
  SurfaceMatchErasesLiteralContentCandidate → ⊥
surfaceMatchDoesNotEraseLiteralContentCandidate ()

data WrongNamespaceMayBorrowPrivateMeaning : Set where
wrongNamespaceMayNotBorrowPrivateMeaning : WrongNamespaceMayBorrowPrivateMeaning → ⊥
wrongNamespaceMayNotBorrowPrivateMeaning ()

data MissingAnchorMayExecutePrivateRule : Set where
missingAnchorMayNotExecutePrivateRule : MissingAnchorMayExecutePrivateRule → ⊥
missingAnchorMayNotExecutePrivateRule ()

data RegistryRevisionRewritesHistoricalRegistry : Set where
registryRevisionDoesNotRewriteHistoricalRegistry :
  RegistryRevisionRewritesHistoricalRegistry → ⊥
registryRevisionDoesNotRewriteHistoricalRegistry ()

------------------------------------------------------------------------
-- Humour-context overlap is a context-selection aid, not command semantics.
------------------------------------------------------------------------

record HumourContextRuntimeProjection : Set where
  constructor humourContextRuntimeProjection
  field
    sourceContext : Grammar.GrammarUseContext
    runtimeNamespaceReference : String
    runtimeContextReference : String
    projectionReference : String

open HumourContextRuntimeProjection public

data HumourContextAloneDeterminesPrivateLexemeMeaning : Set where
humourContextAloneDoesNotDeterminePrivateLexemeMeaning :
  HumourContextAloneDeterminesPrivateLexemeMeaning → ⊥
humourContextAloneDoesNotDeterminePrivateLexemeMeaning ()

------------------------------------------------------------------------
-- Canonical parity boundary.
------------------------------------------------------------------------

record PrivateLexemeRuntimeParityBoundary : Set where
  constructor privateLexemeRuntimeParityBoundary
  field
    namespacesAreExplicit : Bool
    privateLexemeCarriesSurfaceMeaningContextAnchor : Bool
    exactSurfaceMatchRetainsLiteralCandidate : Bool
    requiredAnchorCheckedSeparately : Bool
    wrongNamespaceBlocksExecution : Bool
    missingAnchorRetainsResidual : Bool
    selectedBranchDeletesResidual : Bool
    registryExtensionRewritesHistory : Bool
    humourContextCreatesCommandSemantics : Bool
    runtimeMayEmitCandidateBeforeAdmission : Bool

canonicalPrivateLexemeRuntimeParityBoundary : PrivateLexemeRuntimeParityBoundary
canonicalPrivateLexemeRuntimeParityBoundary =
  privateLexemeRuntimeParityBoundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    true
