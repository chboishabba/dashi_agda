module DASHI.Biology.UrbanPolyphonyThoughtCabinetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.PsychogeographicFieldExact as Field

------------------------------------------------------------------------
-- Fictional design source calibration.
--
-- ZA/UM, Disco Elysium (2019), no DOI assigned.
-- ZA/UM, "Introducing the Thought Cabinet" (2019), no DOI assigned.
--
-- The module abstracts the game's polyphonic skills, Shivers-like urban
-- receptivity, finite thought capacity, ideological projection and co-witness
-- mechanics.  It neither reproduces game text nor claims a city is literally
-- conscious.
------------------------------------------------------------------------

data UrbanSignal : Set where
  windSignal : UrbanSignal
  distantSoundSignal : UrbanSignal
  ruinedArchitectureSignal : UrbanSignal
  streetNameSignal : UrbanSignal
  politicalMonumentSignal : UrbanSignal
  weatherShiftSignal : UrbanSignal

data ObserverFaculty : Set where
  shiversFaculty : ObserverFaculty
  inlandFaculty : ObserverFaculty
  empathyFaculty : ObserverFaculty
  logicFaculty : ObserverFaculty
  authorityFaculty : ObserverFaculty
  halfLightFaculty : ObserverFaculty

data SituatedReading : Set where
  cityCurrentReading : SituatedReading
  symbolicThresholdReading : SituatedReading
  socialPainReading : SituatedReading
  accessRouteReading : SituatedReading
  institutionalDemandReading : SituatedReading
  threatReading : SituatedReading

observeSignal : ObserverFaculty → UrbanSignal → SituatedReading
observeSignal shiversFaculty signal = cityCurrentReading
observeSignal inlandFaculty signal = symbolicThresholdReading
observeSignal empathyFaculty signal = socialPainReading
observeSignal logicFaculty signal = accessRouteReading
observeSignal authorityFaculty signal = institutionalDemandReading
observeSignal halfLightFaculty signal = threatReading

samePassageSupportsPolyphonicReadings :
  ¬ (observeSignal halfLightFaculty ruinedArchitectureSignal
     ≡ observeSignal logicFaculty ruinedArchitectureSignal)
samePassageSupportsPolyphonicReadings ()

shiversIsUrbanFieldReading :
  observeSignal shiversFaculty windSignal ≡ cityCurrentReading
shiversIsUrbanFieldReading = refl

------------------------------------------------------------------------
-- Urban address/response: the same environmental signal may be noticed,
-- interpreted or ignored, changing the next route without making the city a
-- literal subject.
------------------------------------------------------------------------

data AddressResponse : Set where
  noticeResponse : AddressResponse
  interpretResponse : AddressResponse
  ignoreResponse : AddressResponse

routeAfterAddress : UrbanSignal → AddressResponse → Field.RouteStep
routeAfterAddress windSignal noticeResponse = Field.followWaterChannel
routeAfterAddress windSignal interpretResponse = Field.circleChurchThreshold
routeAfterAddress windSignal ignoreResponse = Field.crossSquare
routeAfterAddress distantSoundSignal response = Field.crossSquare
routeAfterAddress ruinedArchitectureSignal response = Field.enterRuin
routeAfterAddress streetNameSignal response = Field.leaveHabitualRoute
routeAfterAddress politicalMonumentSignal response = Field.crossSquare
routeAfterAddress weatherShiftSignal response = Field.returnToHarbour

sameUrbanSignalCanRedirectRoute :
  ¬ (routeAfterAddress windSignal noticeResponse
     ≡ routeAfterAddress windSignal interpretResponse)
sameUrbanSignalCanRedirectRoute ()

------------------------------------------------------------------------
-- Capacity-indexed visibility and the finite Thought Cabinet.
------------------------------------------------------------------------

data Thought : Set where
  revolutionaryResidueThought : Thought
  marketFailureThought : Thought
  ordinarySurvivalThought : Thought
  cityAsInterlocutorThought : Thought
  ruinReoccupationThought : Thought

data ThoughtPhase : Set where
  candidateThought : ThoughtPhase
  researchingThought : ThoughtPhase
  internalisedThought : ThoughtPhase
  inactiveThought : ThoughtPhase

record PlaceAcquiredThought : Set where
  constructor placeAcquiredThought
  field
    thought : Thought
    phase : ThoughtPhase
    sourceSite : Field.Site
    internalisationTime : Nat
    provenance : List String

open PlaceAcquiredThought public

record ThoughtCabinet : Set where
  constructor thoughtCabinet
  field
    activeThoughts : List PlaceAcquiredThought
    capacity : Nat
    cabinetReceipt : String

open ThoughtCabinet public

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

canonicalThoughtCabinet : ThoughtCabinet
canonicalThoughtCabinet =
  thoughtCabinet
    (placeAcquiredThought cityAsInterlocutorThought internalisedThought
      Field.harbourSite 2 ("wind and street history" ∷ [])
    ∷ placeAcquiredThought ruinReoccupationThought researchingThought
      Field.commercialRuinSite 3 ("abandoned commercial interior" ∷ [])
    ∷ [])
    3
    "finite active interpretive loadout"

canonicalCabinetHasTwoActiveThoughts :
  listCount (activeThoughts canonicalThoughtCabinet) ≡ 2
canonicalCabinetHasTwoActiveThoughts = refl

canonicalCabinetCapacityIsThree : capacity canonicalThoughtCabinet ≡ 3
canonicalCabinetCapacityIsThree = refl

canonicalCabinetWithinCapacity :
  listCount (activeThoughts canonicalThoughtCabinet)
  ≤ capacity canonicalThoughtCabinet
canonicalCabinetWithinCapacity = s≤s (s≤s z≤n)

deactivateThought : PlaceAcquiredThought → PlaceAcquiredThought
deactivateThought acquired =
  placeAcquiredThought
    (thought acquired)
    inactiveThought
    (sourceSite acquired)
    (internalisationTime acquired)
    (provenance acquired)

thoughtDeactivationRetainsProvenance :
  (acquired : PlaceAcquiredThought) →
  provenance (deactivateThought acquired) ≡ provenance acquired
thoughtDeactivationRetainsProvenance acquired = refl

thoughtDeactivationRetainsSourceSite :
  (acquired : PlaceAcquiredThought) →
  sourceSite (deactivateThought acquired) ≡ sourceSite acquired
thoughtDeactivationRetainsSourceSite acquired = refl

data VisibleFeature : Set where
  drainageChannelFeature : VisibleFeature
  classConflictFeature : VisibleFeature
  speculativeReuseFeature : VisibleFeature
  surveillanceFeature : VisibleFeature

visibleUnderThought : Thought → VisibleFeature → Bool
visibleUnderThought revolutionaryResidueThought classConflictFeature = true
visibleUnderThought marketFailureThought surveillanceFeature = true
visibleUnderThought ordinarySurvivalThought drainageChannelFeature = true
visibleUnderThought cityAsInterlocutorThought drainageChannelFeature = true
visibleUnderThought ruinReoccupationThought speculativeReuseFeature = true
visibleUnderThought thought feature = false

sameSiteDifferentThoughtsRevealDifferentFeatures :
  visibleUnderThought ruinReoccupationThought speculativeReuseFeature ≡ true
  × visibleUnderThought marketFailureThought speculativeReuseFeature ≡ false
sameSiteDifferentThoughtsRevealDifferentFeatures = refl , refl

------------------------------------------------------------------------
-- Ideology is a projection family, not the material site itself.
------------------------------------------------------------------------

data IdeologyFrame : Set where
  communistFrame : IdeologyFrame
  marketFrame : IdeologyFrame
  moralistFrame : IdeologyFrame
  uncommittedFrame : IdeologyFrame

harbourProjection : IdeologyFrame → Triadic.KernelTrit
harbourProjection communistFrame = Triadic.positiveTrit
harbourProjection marketFrame = Triadic.negativeTrit
harbourProjection moralistFrame = Triadic.zeroTrit
harbourProjection uncommittedFrame = Triadic.zeroTrit

sameHarbourSupportsOpposedIdeologicalProjection :
  ¬ (harbourProjection communistFrame ≡ harbourProjection marketFrame)
sameHarbourSupportsOpposedIdeologicalProjection ()

zeroFrameIsNotDeclaredSynthesis :
  harbourProjection uncommittedFrame ≡ Triadic.zeroTrit
zeroFrameIsNotDeclaredSynthesis = refl

------------------------------------------------------------------------
-- Performed identity crystallises through repeated routes and responses.  It
-- is updated by traversal rather than presupposed as a finished subject.
------------------------------------------------------------------------

data PerformedIdentity : Set where
  undecidedIdentity : PerformedIdentity
  investigatorIdentity : PerformedIdentity
  communalIdentity : PerformedIdentity
  withdrawnIdentity : PerformedIdentity

updateIdentity :
  PerformedIdentity → Field.RouteStep → AddressResponse → PerformedIdentity
updateIdentity identity Field.enterRuin interpretResponse = investigatorIdentity
updateIdentity identity Field.circleChurchThreshold noticeResponse = communalIdentity
updateIdentity identity Field.returnToHarbour ignoreResponse = withdrawnIdentity
updateIdentity identity step response = identity

routeCanCompileDifferentIdentity :
  ¬ (updateIdentity undecidedIdentity Field.enterRuin interpretResponse
     ≡ updateIdentity undecidedIdentity Field.returnToHarbour ignoreResponse)
routeCanCompileDifferentIdentity ()

------------------------------------------------------------------------
-- Co-witnessing preserves agreement or disagreement as typed local sections.
------------------------------------------------------------------------

data WitnessRole : Set where
  primaryWalker : WitnessRole
  trustedCompanion : WitnessRole

data WitnessJudgement : Set where
  agreesJudgement : WitnessJudgement
  disagreesJudgement : WitnessJudgement
  suspendsJudgement : WitnessJudgement

record CoWitnessedUrbanEvent : Set where
  constructor coWitnessedUrbanEvent
  field
    eventLabel : String
    primaryReading companionReading : SituatedReading
    companionJudgement : WitnessJudgement
    provenanceRetained : Bool
    provenanceRetainedIsTrue : provenanceRetained ≡ true

open CoWitnessedUrbanEvent public

canonicalCoWitnessedEvent : CoWitnessedUrbanEvent
canonicalCoWitnessedEvent =
  coWitnessedUrbanEvent
    "ruined passage at night"
    threatReading
    accessRouteReading
    disagreesJudgement
    true refl

coWitnessingDoesNotForceCollapse :
  ¬ (primaryReading canonicalCoWitnessedEvent
     ≡ companionReading canonicalCoWitnessedEvent)
coWitnessingDoesNotForceCollapse ()

record UrbanPolyphonyBoundary : Set where
  constructor urbanPolyphonyBoundary
  field
    cityLiterallyConsciousClaimed : Bool
    cityLiterallyConsciousClaimedIsFalse :
      cityLiterallyConsciousClaimed ≡ false
    oneFacultyIsTotalTruth : Bool
    oneFacultyIsTotalTruthIsFalse : oneFacultyIsTotalTruth ≡ false
    ideologyEqualsMaterialState : Bool
    ideologyEqualsMaterialStateIsFalse : ideologyEqualsMaterialState ≡ false
    participantOrCompanionAgreementIsIndependentVerification : Bool
    participantOrCompanionAgreementIsIndependentVerificationIsFalse :
      participantOrCompanionAgreementIsIndependentVerification ≡ false

canonicalUrbanPolyphonyBoundary : UrbanPolyphonyBoundary
canonicalUrbanPolyphonyBoundary =
  urbanPolyphonyBoundary false refl false refl false refl false refl
