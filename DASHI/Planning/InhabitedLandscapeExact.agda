module DASHI.Planning.InhabitedLandscapeExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- INHABITED LANDSCAPE
--
-- Urban, peri-urban and rural systems share a common situated carrier without
-- collapsing their differences.  Places may carry many simultaneous roles;
-- legal permission and observed use remain distinct; distance is indexed by
-- network/relation rather than assumed to be one universal metric.
------------------------------------------------------------------------

record InhabitedLandscape : Set₁ where
  field
    Place      : Set
    Time       : Set
    Inhabitant : Set
    Resource   : Set
    Function   : Set
    Activity   : Set
    Network    : Set

    Role        : Place → Function → Set
    PermittedUse : Place → Activity → Set
    ObservedUse  : Place → Time → Activity → Set
    ConnectedBy  : Network → Place → Place → Set

open InhabitedLandscape public

data Place : Set where
  marketGarden communityHall creek : Place

data Time : Set where
  wetSeason drySeason : Time

data Inhabitant : Set where
  resident farmer visitor : Inhabitant

data Resource : Set where
  water soil roadAccess : Resource

data Function : Set where
  home workplace foodProduction ecologicalPatch commercialEnterprise
  socialInfrastructure disasterRefuge meetingSpace pollingPlace culturalVenue
  ecosystem drainage boundary recreation floodHazard culturalLandscape : Function

data Activity : Set where
  dwelling farming gathering emergencyShelter recreationUse : Activity

data Network : Set where
  euclidean road emergency ecological : Network

RoleRel : Place → Function → Set
RoleRel marketGarden home = ⊤
RoleRel marketGarden workplace = ⊤
RoleRel marketGarden foodProduction = ⊤
RoleRel marketGarden ecologicalPatch = ⊤
RoleRel marketGarden commercialEnterprise = ⊤
RoleRel communityHall socialInfrastructure = ⊤
RoleRel communityHall disasterRefuge = ⊤
RoleRel communityHall meetingSpace = ⊤
RoleRel communityHall pollingPlace = ⊤
RoleRel communityHall culturalVenue = ⊤
RoleRel creek ecosystem = ⊤
RoleRel creek drainage = ⊤
RoleRel creek boundary = ⊤
RoleRel creek recreation = ⊤
RoleRel creek floodHazard = ⊤
RoleRel creek culturalLandscape = ⊤
RoleRel _ _ = ⊥

Permitted : Place → Activity → Set
Permitted marketGarden farming = ⊤
Permitted communityHall gathering = ⊤
Permitted creek recreationUse = ⊥
Permitted _ _ = ⊥

Observed : Place → Time → Activity → Set
Observed marketGarden wetSeason farming = ⊤
Observed marketGarden drySeason farming = ⊤
Observed communityHall wetSeason gathering = ⊤
Observed creek drySeason recreationUse = ⊤
Observed _ _ _ = ⊥

Connected : Network → Place → Place → Set
Connected euclidean marketGarden creek = ⊤
Connected road marketGarden creek = ⊥
Connected emergency communityHall marketGarden = ⊤
Connected ecological marketGarden creek = ⊤
Connected _ _ _ = ⊥

landscape : InhabitedLandscape
landscape =
  record
    { Place = Place
    ; Time = Time
    ; Inhabitant = Inhabitant
    ; Resource = Resource
    ; Function = Function
    ; Activity = Activity
    ; Network = Network
    ; Role = RoleRel
    ; PermittedUse = Permitted
    ; ObservedUse = Observed
    ; ConnectedBy = Connected
    }

marketGardenIsGenuinelyMultifunctional :
  Role landscape marketGarden home ×
  (Role landscape marketGarden workplace ×
  (Role landscape marketGarden foodProduction ×
  (Role landscape marketGarden ecologicalPatch ×
   Role landscape marketGarden commercialEnterprise)))
marketGardenIsGenuinelyMultifunctional = tt , (tt , (tt , (tt , tt)))

observedUseNeedNotBePermittedUse :
  ObservedUse landscape creek drySeason recreationUse ×
  (PermittedUse landscape creek recreationUse → ⊥)
observedUseNeedNotBePermittedUse = tt , (λ permitted → permitted)

networkRelativeConnectivityDiffers :
  ConnectedBy landscape euclidean marketGarden creek ×
  (ConnectedBy landscape road marketGarden creek → ⊥)
networkRelativeConnectivityDiffers = tt , (λ roadConnection → roadConnection)

------------------------------------------------------------------------
-- Low spatial density is not identified with low systemic complexity.
------------------------------------------------------------------------

data LowDensityImpliesLowComplexityPermission : Set where

lowDensityDoesNotAutoPromoteToLowComplexity :
  LowDensityImpliesLowComplexityPermission → ⊥
lowDensityDoesNotAutoPromoteToLowComplexity ()
