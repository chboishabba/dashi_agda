module DASHI.Biology.AnimalexicAnimalUtteranceSurface where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Empty type for explicitly rejected routes.
------------------------------------------------------------------------

data Never : Set where

------------------------------------------------------------------------
-- Observation and promotion vocabulary.
------------------------------------------------------------------------

data ObservationModality : Set where
  acousticTrace : ObservationModality
  postureTrace : ObservationModality
  motionTrace : ObservationModality
  gazeTrace : ObservationModality
  contactTrace : ObservationModality
  environmentTrace : ObservationModality
  socialTrace : ObservationModality
  physiologicalTrace : ObservationModality

data LatentStateAspect : Set where
  bodyArousal : LatentStateAspect
  painOrDiscomfort : LatentStateAspect
  hungerOrThirst : LatentStateAspect
  affiliativeOrientation : LatentStateAspect
  defensiveOrientation : LatentStateAspect
  dominanceOrSubmission : LatentStateAspect
  playOrientation : LatentStateAspect
  caregivingOrSolicitation : LatentStateAspect
  environmentalAttention : LatentStateAspect

data AnimalexicBoundary : Set where
  noSoundToWordDirectSemantics : AnimalexicBoundary
  noDirectQualiaClaim : AnimalexicBoundary
  noPromotionWithoutReceipts : AnimalexicBoundary
  noSpeciesUniversalDictionary : AnimalexicBoundary
  noHumanLanguageEquivalence : AnimalexicBoundary
  noSingleChannelCertainty : AnimalexicBoundary

data PromotionRoute : Set where
  multimodalLatentReceiptRoute : PromotionRoute
  soundToWordDirectRoute : PromotionRoute
  directQualiaRoute : PromotionRoute
  receiptlessPromotionRoute : PromotionRoute

AdmissibleRoute : PromotionRoute -> Set
AdmissibleRoute multimodalLatentReceiptRoute = ⊤
AdmissibleRoute soundToWordDirectRoute = Never
AdmissibleRoute directQualiaRoute = Never
AdmissibleRoute receiptlessPromotionRoute = Never

soundToWordDirectRejected :
  AdmissibleRoute soundToWordDirectRoute -> Never
soundToWordDirectRejected impossible = impossible

directQualiaRejected :
  AdmissibleRoute directQualiaRoute -> Never
directQualiaRejected impossible = impossible

receiptlessPromotionRejected :
  AdmissibleRoute receiptlessPromotionRoute -> Never
receiptlessPromotionRejected impossible = impossible

------------------------------------------------------------------------
-- Animalexic surface.
------------------------------------------------------------------------

record AnimalexicAnimalUtteranceSurface : Set₁ where
  field
    Animal : Set
    Context : Set
    UtteranceEvent : Set
    ObservationTrace : Set
    BodyStateCandidate : Set
    SocialStateCandidate : Set
    LatentCandidate : Set
    BehaviouralMeaning : Set
    Receipt : Set
    ProvenanceNode : Set
    ObserverProtocol : Set

    observe :
      Animal -> Context -> UtteranceEvent -> ObservationTrace

    observedModalities :
      ObservationTrace -> List ObservationModality

    candidateBodyState :
      ObservationTrace -> BodyStateCandidate

    candidateSocialState :
      ObservationTrace -> SocialStateCandidate

    candidateLatentState :
      ObservationTrace ->
      BodyStateCandidate ->
      SocialStateCandidate ->
      LatentCandidate

    latentAspects :
      LatentCandidate -> List LatentStateAspect

    admissibilityReceipt :
      ObservationTrace -> LatentCandidate -> Receipt

    provenanceTrail :
      Receipt -> List ProvenanceNode

    observerProtocol :
      Receipt -> ObserverProtocol

    promoteBehaviouralMeaning :
      ObservationTrace ->
      LatentCandidate ->
      Receipt ->
      BehaviouralMeaning

    multimodalReceiptComplete :
      ObservationTrace -> LatentCandidate -> Receipt -> Set

    provenanceAdmissible :
      Receipt -> Set

    boundaryReading :
      List AnimalexicBoundary

open AnimalexicAnimalUtteranceSurface public

record AnimalUtteranceObservation
    (surface : AnimalexicAnimalUtteranceSurface) : Set where
  field
    animal : Animal surface
    context : Context surface
    utterance : UtteranceEvent surface
    trace : ObservationTrace surface
    traceIsObserved :
      trace ≡ observe surface animal context utterance
    modalities :
      List ObservationModality
    modalitiesMatch :
      modalities ≡ observedModalities surface trace

open AnimalUtteranceObservation public

record CandidateLatentBodySocialState
    (surface : AnimalexicAnimalUtteranceSurface)
    (observation : AnimalUtteranceObservation surface) : Set where
  field
    bodyCandidate :
      BodyStateCandidate surface
    socialCandidate :
      SocialStateCandidate surface
    latentCandidate :
      LatentCandidate surface
    bodyCandidateMatches :
      bodyCandidate ≡
        candidateBodyState surface (trace observation)
    socialCandidateMatches :
      socialCandidate ≡
        candidateSocialState surface (trace observation)
    latentCandidateMatches :
      latentCandidate ≡
        candidateLatentState
          surface
          (trace observation)
          bodyCandidate
          socialCandidate
    latentAspectEvidence :
      List LatentStateAspect

open CandidateLatentBodySocialState public

record AnimalexicPromotionReceipt
    (surface : AnimalexicAnimalUtteranceSurface)
    (observation : AnimalUtteranceObservation surface)
    (candidate : CandidateLatentBodySocialState surface observation) : Set where
  field
    receipt :
      Receipt surface
    receiptMatchesCandidate :
      receipt ≡
        admissibilityReceipt
          surface
          (trace observation)
          (latentCandidate candidate)
    multimodalGate :
      multimodalReceiptComplete
        surface
        (trace observation)
        (latentCandidate candidate)
        receipt
    provenanceGate :
      provenanceAdmissible surface receipt
    trail :
      List (ProvenanceNode surface)
    trailMatches :
      trail ≡ provenanceTrail surface receipt
    route :
      PromotionRoute
    routeIsReceiptRoute :
      route ≡ multimodalLatentReceiptRoute
    routeAdmissible :
      AdmissibleRoute route

open AnimalexicPromotionReceipt public

record PromotedAnimalexicMeaning
    (surface : AnimalexicAnimalUtteranceSurface)
    (observation : AnimalUtteranceObservation surface)
    (candidate : CandidateLatentBodySocialState surface observation)
    (receipt : AnimalexicPromotionReceipt surface observation candidate) : Set where
  field
    meaning :
      BehaviouralMeaning surface
    meaningMatchesPromotion :
      meaning ≡
        promoteBehaviouralMeaning
          surface
          (trace observation)
          (latentCandidate candidate)
          (AnimalexicPromotionReceipt.receipt receipt)
    promotedBehaviourOnly :
      Bool
    promotedBehaviourOnlyIsTrue :
      promotedBehaviourOnly ≡ true
    directWordSemanticsRecovered :
      Bool
    directWordSemanticsRecoveredIsFalse :
      directWordSemanticsRecovered ≡ false
    directQualiaRecovered :
      Bool
    directQualiaRecoveredIsFalse :
      directQualiaRecovered ≡ false

open PromotedAnimalexicMeaning public

promoteWithReceipts :
  (surface : AnimalexicAnimalUtteranceSurface) ->
  (observation : AnimalUtteranceObservation surface) ->
  (candidate : CandidateLatentBodySocialState surface observation) ->
  (receipt : AnimalexicPromotionReceipt surface observation candidate) ->
  BehaviouralMeaning surface
promoteWithReceipts surface observation candidate receipt =
  promoteBehaviouralMeaning
    surface
    (trace observation)
    (latentCandidate candidate)
    (AnimalexicPromotionReceipt.receipt receipt)

canonicalRouteAdmissible :
  AdmissibleRoute multimodalLatentReceiptRoute
canonicalRouteAdmissible = tt

canonicalAnimalexicBoundaries : List AnimalexicBoundary
canonicalAnimalexicBoundaries =
  noSoundToWordDirectSemantics ∷
  noDirectQualiaClaim ∷
  noPromotionWithoutReceipts ∷
  noSpeciesUniversalDictionary ∷
  noHumanLanguageEquivalence ∷
  noSingleChannelCertainty ∷
  []
