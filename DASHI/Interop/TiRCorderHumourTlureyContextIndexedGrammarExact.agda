module DASHI.Interop.TiRCorderHumourTlureyContextIndexedGrammarExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Interop.TiRCorderVoiceEditInteroceptionAntiPanopticonExact as Voice
import DASHI.Interop.TiRCorderSpokenIntentGrammarRuddCrossPollinationExact as Rudd
import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Reasoning.HumourRelationRepresentationCrossPollinationExact as HumourRR
import LogicTlurey as TlureyTrace
import DASHI.Cognition.TlureyNumerologyStateSpace as TlureyState
import DASHI.Cognition.TlureyDyadicNonaryTraceReceipt as TlureyReceipt

------------------------------------------------------------------------
-- TIRCORDER x HUMOUR x ACTUAL TLUREY CORE
--
-- Correction to the first version of this owner:
-- the relevant Tlurey core is NOT the later RelationalProtocol reinterpretation.
-- The in-repo Tlurey owners used here are:
--
--   LogicTlurey
--     seed -> counter -> resonance -> overflow -> seed
--     with periodic StageTrace and triadic stageTone compression;
--
--   TlureyNumerologyStateSpace
--     recursive hidden state, lossy binary quotient/residual structure,
--     and private TlureyLexeme values carrying surface, intendedMeaning,
--     contextualUse, and requiresSharedAnchor;
--
--   TlureyDyadicNonaryTraceReceipt
--     promotes dyadic recursive branch structure while retaining hidden
--     residual and keeping richer triadic/nonary interpretations candidate-only.
--
-- Humour contributes a separate source-bound context family (rationale,
-- presenter, audience/context, content, delivery, humour type, feedback).
-- The useful compound is therefore an anchor/context indexed private grammar
-- whose public surface is a lossy projection of a richer candidate state.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Humour context coordinates remain source-bound context inputs.
------------------------------------------------------------------------

record GrammarUseContext : Set where
  constructor grammarUseContext
  field
    rationaleReference : String
    presenterReference : String
    audienceContextReference : String
    contentReference : String
    deliveryReference : String
    humourTypeReference : String
    feedbackReference : String

open GrammarUseContext public

------------------------------------------------------------------------
-- 2. Tlurey private lexeme becomes the direct grammar analogue.
--
-- A spoken shorthand is not globally meaningful.  Its surface form is paired
-- with intended meaning, contextual use and a shared-anchor requirement.
------------------------------------------------------------------------

record SpokenPrivateLexeme : Set where
  constructor spokenPrivateLexeme
  field
    tlureyLexeme : TlureyState.TlureyLexeme
    grammarRuleReference : String
    proposedFibre : Voice.SpokenIntentFibre
    proposedEditKind : Voice.VoiceEditKind
    sourceProvenanceReference : String

open SpokenPrivateLexeme public

record SharedAnchorReceipt : Set where
  constructor sharedAnchorReceipt
  field
    lexemeSurfaceReference : String
    speakerReference : String
    grammarNamespaceReference : String
    contextReference : String
    sharedAnchorReference : String
    replayReference : String

open SharedAnchorReceipt public

------------------------------------------------------------------------
-- 3. Surface match is a quotient-like observation, not full meaning.
------------------------------------------------------------------------

record GrammarSurfaceObservation : Set where
  constructor grammarSurfaceObservation
  field
    utteranceReference : String
    matchedSurfaceReference : String
    candidateCount : Nat
    hiddenResidualReference : String
    quotientReference : String

open GrammarSurfaceObservation public

data SurfaceMatchDeterminesIntendedMeaning : Set where
surfaceMatchDoesNotDetermineIntendedMeaning : SurfaceMatchDeterminesIntendedMeaning → ⊥
surfaceMatchDoesNotDetermineIntendedMeaning ()

data SurfaceMatchErasesResidual : Set where
surfaceMatchDoesNotEraseResidual : SurfaceMatchErasesResidual → ⊥
surfaceMatchDoesNotEraseResidual ()

data PrivateLexemePromotesToPublicTruth : Set where
privateLexemeDoesNotPromoteToPublicTruth : PrivateLexemePromotesToPublicTruth → ⊥
privateLexemeDoesNotPromoteToPublicTruth ()

------------------------------------------------------------------------
-- 4. Recursive branch fibre.
--
-- The executable candidate is one branch of a recursive hidden state-space.
-- Other branches remain inspectable residual rather than being destroyed by
-- selecting a winner.
------------------------------------------------------------------------

data SpokenGrammarBranchKind : Set where
  literalContentBranch : SpokenGrammarBranchKind
  formattingCommandBranch : SpokenGrammarBranchKind
  selfCorrectionBranch : SpokenGrammarBranchKind
  discourseMarkerBranch : SpokenGrammarBranchKind
  quotedSpeechBranch : SpokenGrammarBranchKind
  asrArtifactBranch : SpokenGrammarBranchKind
  unresolvedBranch : SpokenGrammarBranchKind

record SpokenGrammarBranch : Set where
  constructor spokenGrammarBranch
  field
    branchIndex : Nat
    kind : SpokenGrammarBranchKind
    candidateReference : String
    confidenceReference : String
    residualReference : String

open SpokenGrammarBranch public

record RecursiveGrammarState : Set where
  constructor recursiveGrammarState
  field
    surfaceObservation : GrammarSurfaceObservation
    recursiveDepth : Nat
    branches : List SpokenGrammarBranch
    selectedBranchReference : String
    residualBranchesReference : String

open RecursiveGrammarState public

data SelectedBranchDeletesAlternatives : Set where
selectedBranchDoesNotDeleteAlternatives : SelectedBranchDeletesAlternatives → ⊥
selectedBranchDoesNotDeleteAlternatives ()

------------------------------------------------------------------------
-- 5. Tlurey stage trace as revision/search phase, not semantic authority.
--
-- We reuse the actual cyclic stage carrier only as a process coordinate:
-- seed -> counter -> resonance -> overflow -> seed.
-- No stage name is claimed to prove command meaning.
------------------------------------------------------------------------

record GrammarStageReceipt : Set where
  constructor grammarStageReceipt
  field
    stage : TlureyTrace.Stage
    stageReference : String
    candidateSetReference : String
    residualReference : String

open GrammarStageReceipt public

data StageToneDeterminesCommandMeaning : Set where
stageToneDoesNotDetermineCommandMeaning : StageToneDeterminesCommandMeaning → ⊥
stageToneDoesNotDetermineCommandMeaning ()

canonicalFourStageTrace : List TlureyTrace.Stage
canonicalFourStageTrace = TlureyTrace.StageTrace 4 TlureyTrace.seed

------------------------------------------------------------------------
-- 6. Context/anchor admission.
--
-- Registration is deliberately weaker than applicability.  A private command
-- may exist in the lexicon but still require a shared anchor for this user,
-- namespace and context before it can be offered for edit admission.
------------------------------------------------------------------------

record AnchoredGrammarCandidate : Set where
  constructor anchoredGrammarCandidate
  field
    lexeme : SpokenPrivateLexeme
    useContext : GrammarUseContext
    sharedAnchor : SharedAnchorReceipt
    candidateReference : String
    residualReference : String
    candidateOnly : Bool

open AnchoredGrammarCandidate public

data RegisteredPrivateLexemeExecutesGlobally : Set where
registeredPrivateLexemeDoesNotExecuteGlobally :
  RegisteredPrivateLexemeExecutesGlobally → ⊥
registeredPrivateLexemeDoesNotExecuteGlobally ()

data SharedAnchorDeterminesCorrectAction : Set where
sharedAnchorDoesNotDetermineCorrectAction : SharedAnchorDeterminesCorrectAction → ⊥
sharedAnchorDoesNotDetermineCorrectAction ()

------------------------------------------------------------------------
-- 7. Humour consumer-relativity applies to grammar projections too.
------------------------------------------------------------------------

data OneContextAdequacyImpliesAllContextAdequacy : Set where
oneContextAdequacyDoesNotImplyAllContextAdequacy :
  OneContextAdequacyImpliesAllContextAdequacy → ⊥
oneContextAdequacyDoesNotImplyAllContextAdequacy ()

humourSourceAnchor : Humour.HumourFrameworkSourceSurface
humourSourceAnchor = Humour.canonicalHumourFrameworkSourceSurface

humourConsumerSafetyAnchor : HumourRR.HumourRelationRepresentationBoundary
humourConsumerSafetyAnchor = HumourRR.canonicalHumourRelationRepresentationBoundary

------------------------------------------------------------------------
-- 8. Actual Tlurey owner anchors.
------------------------------------------------------------------------

tlureyPrivateLanguageIsPrivate : Bool
tlureyPrivateLanguageIsPrivate = TlureyState.tlureyIsPrivateLanguage

tlureyPrivateLanguageIsExternalTruth : Bool
tlureyPrivateLanguageIsExternalTruth = TlureyState.tlureyIsExternalTruth

tlureyTraceReceiptAnchor : TlureyReceipt.DyadicNonaryTraceReceipt
tlureyTraceReceiptAnchor = TlureyReceipt.canonicalTraceReceipt

------------------------------------------------------------------------
-- 9. Integration boundary.
------------------------------------------------------------------------

record TlureyIndexedGrammarBoundary : Set where
  constructor tlureyIndexedGrammarBoundary
  field
    privateLexemeCarriesContextualMeaning : Bool
    privateLexemeRequiresSharedAnchor : Bool
    exactSurfaceMatchDeterminesMeaning : Bool
    exactSurfaceMatchErasesResidual : Bool
    selectedCandidateDeletesOtherBranches : Bool
    stageToneCreatesSemanticAuthority : Bool
    privateLexemeCreatesPublicTruth : Bool
    dyadicRecursiveBranchingReused : Bool
    hiddenResidualRetained : Bool
    humourContextRemainsConsumerRelative : Bool
    verbatimCarrierRemainsPrior : Bool

canonicalTlureyIndexedGrammarBoundary : TlureyIndexedGrammarBoundary
canonicalTlureyIndexedGrammarBoundary =
  tlureyIndexedGrammarBoundary
    true
    true
    false
    false
    false
    false
    false
    true
    true
    true
    true

voiceBoundaryAnchor : Voice.TiRCorderVoiceEditInteroceptionBoundary
voiceBoundaryAnchor = Voice.canonicalTiRCorderVoiceEditInteroceptionBoundary

ruddGrammarBoundaryAnchor : Rudd.SpokenIntentInterpreterBoundary
ruddGrammarBoundaryAnchor = Rudd.canonicalSpokenIntentInterpreterBoundary
