module DASHI.Biology.PsychogeographicFieldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source calibration.
--
-- Guy Debord, "Theory of the Derive" (1956), no DOI assigned.
-- Guy Debord and Gil J. Wolman, "A User's Guide to Detournement" (1956),
-- no DOI assigned.
-- Henri Lefebvre, The Production of Space (1974; English translation 1991),
-- no DOI assigned to the book edition used here.
--
-- The imported structure is bounded: a derive is represented as a path whose
-- lived result depends on route, context and prior state.  No claim is made
-- that the finite carrier is a complete sociology, geography or dynamics of
-- an actual city.
------------------------------------------------------------------------

data SpatialScale : Set where
  bodyFootingScale : SpatialScale
  intimateLocalityScale : SpatialScale
  streetThresholdScale : SpatialScale
  civicInterfaceScale : SpatialScale
  districtOrganisationScale : SpatialScale
  historicalHorizonScale : SpatialScale

data Site : Set where
  squareSite : Site
  bridgeSite : Site
  churchSite : Site
  harbourSite : Site
  commercialRuinSite : Site

data WalkerPhase : Set where
  habitualPhase : WalkerPhase
  attentivePhase : WalkerPhase
  recalledPhase : WalkerPhase
  reorganisedPhase : WalkerPhase

data FieldPolarity : Set where
  attractiveField : FieldPolarity
  repulsiveField : FieldPolarity
  ambivalentField : FieldPolarity

data RouteStep : Set where
  leaveHabitualRoute : RouteStep
  crossSquare : RouteStep
  followWaterChannel : RouteStep
  circleChurchThreshold : RouteStep
  enterRuin : RouteStep
  returnToHarbour : RouteStep

record LivedPlaceState : Set where
  constructor livedPlaceState
  field
    site : Site
    phase : WalkerPhase
    timeIndex : Nat
    affectiveIntensity : Nat
    memoryActivation : Nat
    actionAffordance : Nat
    fieldPolarity : FieldPolarity
    provenance : List String

open LivedPlaceState public

record DeriveTrace : Set where
  constructor deriveTrace
  field
    initialState : LivedPlaceState
    visitedSteps : List RouteStep
    finalState : LivedPlaceState
    traceLabel : String

open DeriveTrace public

habitualHarbourState : LivedPlaceState
habitualHarbourState =
  livedPlaceState harbourSite habitualPhase 0 1 0 1 ambivalentField
    ("harbour material carrier" ∷ [])

recalledChurchState : LivedPlaceState
recalledChurchState =
  livedPlaceState churchSite recalledPhase 3 5 7 2 repulsiveField
    ("square -> water -> church" ∷ [])

reorganisedChurchState : LivedPlaceState
reorganisedChurchState =
  livedPlaceState churchSite reorganisedPhase 4 4 7 6 ambivalentField
    ("ruin -> church reoccupation" ∷ [])

memoryRoute : DeriveTrace
memoryRoute =
  deriveTrace habitualHarbourState
    (leaveHabitualRoute ∷ crossSquare ∷ followWaterChannel ∷ circleChurchThreshold ∷ [])
    recalledChurchState
    "memory-bearing route"

reoccupationRoute : DeriveTrace
reoccupationRoute =
  deriveTrace habitualHarbourState
    (leaveHabitualRoute ∷ enterRuin ∷ circleChurchThreshold ∷ [])
    reorganisedChurchState
    "reoccupation-bearing route"

samePhysicalEndpoint : site (finalState memoryRoute) ≡ site (finalState reoccupationRoute)
samePhysicalEndpoint = refl

sameEndpointDoesNotForceSamePhase :
  ¬ (phase (finalState memoryRoute) ≡ phase (finalState reoccupationRoute))
sameEndpointDoesNotForceSamePhase ()

sameEndpointDoesNotForceSameAffordance :
  ¬ (actionAffordance (finalState memoryRoute)
     ≡ actionAffordance (finalState reoccupationRoute))
sameEndpointDoesNotForceSameAffordance ()

------------------------------------------------------------------------
-- A finite detournement witness retains one material carrier while changing
-- its organised use and social relation.
------------------------------------------------------------------------

data UrbanUse : Set where
  commercialUse : UrbanUse
  shelterUse : UrbanUse
  assemblyUse : UrbanUse
  memorialUse : UrbanUse
  danceResearchUse : UrbanUse

data SignContext : Set where
  advertisingContext : SignContext
  protestContext : SignContext
  memorialContext : SignContext

record DetournementWitness : Set where
  constructor detournementWitness
  field
    retainedCarrier : Site
    beforeUse afterUse : UrbanUse
    beforeContext afterContext : SignContext
    changedRelationReceipt : String

open DetournementWitness public

canonicalDetournement : DetournementWitness
canonicalDetournement =
  detournementWitness commercialRuinSite commercialUse assemblyUse
    advertisingContext protestContext
    "same built carrier; altered sign-place-action relation"

canonicalDetournementRetainsCarrier :
  retainedCarrier canonicalDetournement ≡ commercialRuinSite
canonicalDetournementRetainsCarrier = refl

canonicalDetournementChangesUse :
  ¬ (beforeUse canonicalDetournement ≡ afterUse canonicalDetournement)
canonicalDetournementChangesUse ()

------------------------------------------------------------------------
-- Attraction and repulsion are components of a lived local potential rather
-- than intrinsic scalar properties of the material site.
------------------------------------------------------------------------

record PsychogeographicPotential : Set where
  constructor psychogeographicPotential
  field
    architecturalContribution : Nat
    socialContribution : Nat
    memoryContribution : Nat
    symbolicContribution : Nat

open PsychogeographicPotential public

totalPotential : PsychogeographicPotential → Nat
totalPotential potential =
  architecturalContribution potential
  + socialContribution potential
  + memoryContribution potential
  + symbolicContribution potential

habitualHarbourPotential : PsychogeographicPotential
habitualHarbourPotential = psychogeographicPotential 1 2 0 1

recalledChurchPotential : PsychogeographicPotential
recalledChurchPotential = psychogeographicPotential 2 1 7 4

habitualHarbourPotentialIsFour : totalPotential habitualHarbourPotential ≡ 4
habitualHarbourPotentialIsFour = refl

recalledChurchPotentialIsFourteen : totalPotential recalledChurchPotential ≡ 14
recalledChurchPotentialIsFourteen = refl

sameMaterialCategoryNeedNotHaveSameLivedPotential :
  ¬ (totalPotential habitualHarbourPotential
     ≡ totalPotential recalledChurchPotential)
sameMaterialCategoryNeedNotHaveSameLivedPotential ()

record PsychogeographicFieldBoundary : Set where
  constructor psychogeographicFieldBoundary
  field
    endpointDeterminesLivedResult : Bool
    endpointDeterminesLivedResultIsFalse :
      endpointDeterminesLivedResult ≡ false
    materialCarrierMustBeDestroyedToChangeMeaning : Bool
    materialCarrierMustBeDestroyedToChangeMeaningIsFalse :
      materialCarrierMustBeDestroyedToChangeMeaning ≡ false
    finiteTraceIsCompleteUrbanDynamics : Bool
    finiteTraceIsCompleteUrbanDynamicsIsFalse :
      finiteTraceIsCompleteUrbanDynamics ≡ false
    routeHistoryMayChangeAffordance : Bool
    routeHistoryMayChangeAffordanceIsTrue :
      routeHistoryMayChangeAffordance ≡ true

canonicalPsychogeographicFieldBoundary : PsychogeographicFieldBoundary
canonicalPsychogeographicFieldBoundary =
  psychogeographicFieldBoundary false refl false refl false refl true refl
