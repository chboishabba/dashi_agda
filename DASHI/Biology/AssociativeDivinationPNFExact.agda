module DASHI.Biology.AssociativeDivinationPNFExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DASHIYijingTernaryDivinationExact as Yijing

------------------------------------------------------------------------
-- Epistemically typed reading techniques.

data ReadingEvidenceSource : Set where
  symbolicCast : ReadingEvidenceSource
  coldCue : ReadingEvidenceSource
  warmBaseRate : ReadingEvidenceSource
  hotPriorInformation : ReadingEvidenceSource
  participantCompletion : ReadingEvidenceSource
  readerPatternRecognition : ReadingEvidenceSource

data ParticipantSignal : Set where
  rejects : ParticipantSignal
  neutral : ParticipantSignal
  weaklyConfirms : ParticipantSignal
  stronglyConfirms : ParticipantSignal

signalWeight : ParticipantSignal → Nat
signalWeight rejects = 0
signalWeight neutral = 1
signalWeight weaklyConfirms = 2
signalWeight stronglyConfirms = 3

record InteractiveReadingState : Set where
  constructor interactiveReadingState
  field
    currentHypothesis : Nat
    confidence : Nat
    evidenceTrace : List ReadingEvidenceSource

open InteractiveReadingState public

updateFromParticipant :
  InteractiveReadingState → ParticipantSignal → InteractiveReadingState
updateFromParticipant
  (interactiveReadingState hypothesis score trace)
  response =
  interactiveReadingState
    hypothesis
    (score + signalWeight response)
    (participantCompletion ∷ trace)

canonicalInitialReadingState : InteractiveReadingState
canonicalInitialReadingState =
  interactiveReadingState 7 1
    (symbolicCast ∷ readerPatternRecognition ∷ [])

canonicalConfirmedReadingState : InteractiveReadingState
canonicalConfirmedReadingState =
  updateFromParticipant canonicalInitialReadingState stronglyConfirms

participantFeedbackRaisesFiniteConfidence :
  confidence canonicalConfirmedReadingState ≡ 4
participantFeedbackRaisesFiniteConfidence = refl

feedbackAddsParticipantCompletionToTrace :
  evidenceTrace canonicalConfirmedReadingState
  ≡ participantCompletion
    ∷ symbolicCast
    ∷ readerPatternRecognition
    ∷ []
feedbackAddsParticipantCompletionToTrace = refl

------------------------------------------------------------------------
-- Psychoanalytic/free-associative use: the informative object is what the
-- participant selects, rejects, elaborates, fears, or links, not an externally
-- verified oracle channel.

data AssociativeResponse : Set where
  selectedAssociation : AssociativeResponse
  rejectedAssociation : AssociativeResponse
  elaboratedAssociation : AssociativeResponse
  affectiveAssociation : AssociativeResponse
  noAssociation : AssociativeResponse

data InterpretiveClaimKind : Set where
  structuralClaim : InterpretiveClaimKind
  autobiographicalHypothesis : InterpretiveClaimKind
  therapeuticPrompt : InterpretiveClaimKind
  externalHiddenFactClaim : InterpretiveClaimKind

record AssociationTrace : Set where
  constructor associationTrace
  field
    castContext : Nat
    response : AssociativeResponse
    claimKind : InterpretiveClaimKind
    communicatedByReader : Bool
    externallyVerified : Bool

open AssociationTrace public

canonicalFreeAssociationTrace : AssociationTrace
canonicalFreeAssociationTrace =
  associationTrace
    1
    elaboratedAssociation
    autobiographicalHypothesis
    true
    false

------------------------------------------------------------------------
-- Predicate-normal-form compilation keeps structural, associative, and
-- externally predictive claims in different constructors.

data PNFAtom : Set where
  castProduced : Nat → PNFAtom
  participantSelected : Nat → PNFAtom
  participantRejected : Nat → PNFAtom
  readerObservedCue : Nat → PNFAtom
  baseRateApplied : Nat → PNFAtom
  priorInformationUsed : Nat → PNFAtom
  autobiographicalThemeHypothesized : Nat → PNFAtom
  externalEventPredicted : Nat → PNFAtom
  externalEventVerified : Nat → PNFAtom

compileAssociationPNF : AssociationTrace → List PNFAtom
compileAssociationPNF
  (associationTrace context selectedAssociation kind communicated verified) =
  castProduced context
  ∷ participantSelected context
  ∷ autobiographicalThemeHypothesized context
  ∷ []
compileAssociationPNF
  (associationTrace context rejectedAssociation kind communicated verified) =
  castProduced context
  ∷ participantRejected context
  ∷ []
compileAssociationPNF
  (associationTrace context elaboratedAssociation kind communicated verified) =
  castProduced context
  ∷ participantSelected context
  ∷ autobiographicalThemeHypothesized context
  ∷ []
compileAssociationPNF
  (associationTrace context affectiveAssociation kind communicated verified) =
  castProduced context
  ∷ participantSelected context
  ∷ autobiographicalThemeHypothesized context
  ∷ []
compileAssociationPNF
  (associationTrace context noAssociation kind communicated verified) =
  castProduced context ∷ []

canonicalAssociationCompilesWithoutExternalPrediction :
  compileAssociationPNF canonicalFreeAssociationTrace
  ≡ castProduced 1
    ∷ participantSelected 1
    ∷ autobiographicalThemeHypothesized 1
    ∷ []
canonicalAssociationCompilesWithoutExternalPrediction = refl

------------------------------------------------------------------------
-- Story/place/multimodal memory fibres.

data RetrievalFibre : Set where
  placeFibre : RetrievalFibre
  storyFibre : RetrievalFibre
  rhythmFibre : RetrievalFibre
  imageFibre : RetrievalFibre
  kinshipFibre : RetrievalFibre
  ecologicalFibre : RetrievalFibre

canonicalNarrativeRetrievalFibres : List RetrievalFibre
canonicalNarrativeRetrievalFibres =
  placeFibre
  ∷ storyFibre
  ∷ rhythmFibre
  ∷ imageFibre
  ∷ kinshipFibre
  ∷ ecologicalFibre
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

canonicalNarrativeHasSixRetrievalFibres :
  listCount canonicalNarrativeRetrievalFibres ≡ 6
canonicalNarrativeHasSixRetrievalFibres = refl

record AssociativeDivinationBoundary : Set where
  constructor associativeDivinationBoundary
  field
    participantConfirmationIsIndependentExternalVerification : Bool
    participantConfirmationIsIndependentExternalVerificationIsFalse :
      participantConfirmationIsIndependentExternalVerification ≡ false

    skilledPatternRecognitionRequiresFraud : Bool
    skilledPatternRecognitionRequiresFraudIsFalse :
      skilledPatternRecognitionRequiresFraud ≡ false

    accurateSocialInferenceEntailsParanormalChannel : Bool
    accurateSocialInferenceEntailsParanormalChannelIsFalse :
      accurateSocialInferenceEntailsParanormalChannel ≡ false

    psychoanalyticAssociationIsRecoveredMemoryAuthority : Bool
    psychoanalyticAssociationIsRecoveredMemoryAuthorityIsFalse :
      psychoanalyticAssociationIsRecoveredMemoryAuthority ≡ false

    indigenousKnowledgeIsOnlyMnemonicTechnique : Bool
    indigenousKnowledgeIsOnlyMnemonicTechniqueIsFalse :
      indigenousKnowledgeIsOnlyMnemonicTechnique ≡ false

    storyCanProvideMultipleRetrievalIndices : Bool
    storyCanProvideMultipleRetrievalIndicesIsTrue :
      storyCanProvideMultipleRetrievalIndices ≡ true

open AssociativeDivinationBoundary public

canonicalAssociativeDivinationBoundary : AssociativeDivinationBoundary
canonicalAssociativeDivinationBoundary =
  associativeDivinationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
