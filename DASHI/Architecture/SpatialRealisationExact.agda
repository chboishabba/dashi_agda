module DASHI.Architecture.SpatialRealisationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- SPATIAL REALISATION
--
-- Shared abstract carrier for buildings, settlements, fabs and chip physical
-- design.  It deliberately separates placement, required relation, routing,
-- local validity, global routability and capacity safety.
------------------------------------------------------------------------

record SpatialRealisationSystem : Set₁ where
  field
    Component : Set
    Site      : Set
    Relation  : Set
    Path      : Set

    place     : Component → Site
    requires  : Relation → Component → Component → Set
    route     : Relation → Path

    LocallyValid     : Set
    GloballyRoutable : Set
    CapacitySafe     : Set

open SpatialRealisationSystem public

record AdmissibleSpatialRealisation
    (system : SpatialRealisationSystem) : Set₁ where
  field
    locallyValid     : LocallyValid system
    globallyRoutable : GloballyRoutable system
    capacitySafe     : CapacitySafe system

open AdmissibleSpatialRealisation public

------------------------------------------------------------------------
-- Local validity does not manufacture global routability.
------------------------------------------------------------------------

data LocalValidityImpliesGlobalRoutabilityPermission : Set where

localValidityDoesNotAutoPromoteToGlobalRoutability :
  LocalValidityImpliesGlobalRoutabilityPermission → ⊥
localValidityDoesNotAutoPromoteToGlobalRoutability ()

------------------------------------------------------------------------
-- Concrete finite witness: two individually placeable components share one
-- exhausted route.  This is a theorem about the abstract carrier, not a claim
-- that every urban/chip instance has this exact topology.
------------------------------------------------------------------------

data ToyComponent : Set where
  componentA componentB : ToyComponent

data ToySite : Set where
  siteA siteB : ToySite

data ToyRelation : Set where
  sharedCorridor : ToyRelation

data ToyPath : Set where
  oneCorridor : ToyPath

data ToyLocal : Set where
  locallyOK : ToyLocal

data ToyGlobal : Set where

data ToyCapacity : Set where
  capacityWitness : ToyCapacity

toySystem : SpatialRealisationSystem
toySystem =
  record
    { Component = ToyComponent
    ; Site = ToySite
    ; Relation = ToyRelation
    ; Path = ToyPath
    ; place = λ where
        componentA → siteA
        componentB → siteB
    ; requires = λ _ _ _ → ⊤
    ; route = λ _ → oneCorridor
    ; LocallyValid = ToyLocal
    ; GloballyRoutable = ToyGlobal
    ; CapacitySafe = ToyCapacity
    }

toyPlacementIsLocallyValid : LocallyValid toySystem
toyPlacementIsLocallyValid = locallyOK

toyPlacementIsNotGloballyRoutable : GloballyRoutable toySystem → ⊥
toyPlacementIsNotGloballyRoutable ()

locallyValidPlacementNeedNotBeGloballyRoutable :
  LocallyValid toySystem × (GloballyRoutable toySystem → ⊥)
locallyValidPlacementNeedNotBeGloballyRoutable =
  toyPlacementIsLocallyValid , toyPlacementIsNotGloballyRoutable
