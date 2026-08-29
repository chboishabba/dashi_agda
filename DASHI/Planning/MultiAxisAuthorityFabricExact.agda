module DASHI.Planning.MultiAxisAuthorityFabricExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- MULTI-AXIS AUTHORITY FABRIC / NON-CONTAINMENT
------------------------------------------------------------------------

data AuthorityAxis : Set where
  landAxis heritageAxis planningAxis infrastructureAxis ecologyAxis
  knowledgeAxis practiceAxis consentAxis : AuthorityAxis

data AuthorityNode : Set where
  stateAuthority custodialAuthority communityAuthority technicalAuthority : AuthorityNode

CanDecide : AuthorityNode → AuthorityAxis → Set
CanDecide stateAuthority planningAxis = ⊤
CanDecide stateAuthority infrastructureAxis = ⊤
CanDecide custodialAuthority landAxis = ⊤
CanDecide custodialAuthority heritageAxis = ⊤
CanDecide custodialAuthority knowledgeAxis = ⊤
CanDecide custodialAuthority practiceAxis = ⊤
CanDecide custodialAuthority consentAxis = ⊤
CanDecide communityAuthority consentAxis = ⊤
CanDecide technicalAuthority infrastructureAxis = ⊤
CanDecide _ _ = ⊥

statePlanningPowerDoesNotCreateHeritageAuthority :
  CanDecide stateAuthority heritageAxis → ⊥
statePlanningPowerDoesNotCreateHeritageAuthority x = x

technicalInfrastructureCompetenceDoesNotCreateConsentAuthority :
  CanDecide technicalAuthority consentAxis → ⊥
technicalInfrastructureCompetenceDoesNotCreateConsentAuthority x = x

data SpatiallyContains : AuthorityNode → AuthorityNode → Set where
  administrativeContainsCustodial : SpatiallyContains stateAuthority custodialAuthority

data SpatialContainmentImpliesAuthorityContainmentPermission : Set where
spatialContainmentCannotAutoPromoteAuthority :
  SpatialContainmentImpliesAuthorityContainmentPermission → ⊥
spatialContainmentCannotAutoPromoteAuthority ()

record AuthorityFabricBoundary : Set where
  constructor authorityFabricBoundary
  field
    oneAxisJurisdictionImpliesAllAxes : Bool
    oneAxisJurisdictionImpliesAllAxesIsFalse : oneAxisJurisdictionImpliesAllAxes ≡ false
    spatialContainmentImpliesAuthorityContainment : Bool
    spatialContainmentImpliesAuthorityContainmentIsFalse :
      spatialContainmentImpliesAuthorityContainment ≡ false
    technicalCompetenceImpliesConsentAuthority : Bool
    technicalCompetenceImpliesConsentAuthorityIsFalse :
      technicalCompetenceImpliesConsentAuthority ≡ false

canonicalAuthorityFabricBoundary : AuthorityFabricBoundary
canonicalAuthorityFabricBoundary = authorityFabricBoundary false refl false refl false refl
