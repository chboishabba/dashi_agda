module DASHI.Planning.DataCentreUrbanResourceConflictExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- DATA-CENTRE / URBAN RESOURCE CONFLICT
--
-- This file encodes the generic planning structure exposed by AI data-centre
-- disputes.  It does not assert corruption, illegality, climate harm or social
-- illegitimacy of any concrete project.  Those require source-bound evidence.
------------------------------------------------------------------------

data Project : Set where
  housingProject aiDataCentre : Project

data Resource : Set where
  land electricity water infrastructure labour capital : Resource

data Location : Set where
  housingSite industrialSite : Location

Demand : Project → Resource → Set
Demand housingProject land = ⊤
Demand housingProject electricity = ⊤
Demand housingProject water = ⊤
Demand housingProject infrastructure = ⊤
Demand housingProject labour = ⊤
Demand housingProject capital = ⊤
Demand aiDataCentre land = ⊤
Demand aiDataCentre electricity = ⊤
Demand aiDataCentre water = ⊤
Demand aiDataCentre infrastructure = ⊤
Demand aiDataCentre labour = ⊤
Demand aiDataCentre capital = ⊤

LocatedAt : Project → Location
LocatedAt housingProject = housingSite
LocatedAt aiDataCentre = industrialSite

data SpatiallyOverlaps : Project → Project → Set where

CompetesFor : Project → Project → Resource → Set
CompetesFor left right resource = Demand left resource × Demand right resource

projectsNeedNotOverlapToCompeteForElectricity :
  (SpatiallyOverlaps housingProject aiDataCentre → ⊥) ×
  CompetesFor housingProject aiDataCentre electricity
projectsNeedNotOverlapToCompeteForElectricity =
  (λ overlap → overlap) , (tt , tt)

noSpatialOverlapDoesNotImplyNoPlanningConflict :
  (SpatiallyOverlaps housingProject aiDataCentre → ⊥) ×
  CompetesFor housingProject aiDataCentre infrastructure
noSpatialOverlapDoesNotImplyNoPlanningConflict =
  (λ overlap → overlap) , (tt , tt)

------------------------------------------------------------------------
-- Observer/authority projections remain distinct while resource coupling may
-- cross all of them.
------------------------------------------------------------------------

data Observer : Set where
  operator grid city climate community : Observer

data ProjectView : Set where
  computeCapacity gridLoad infrastructureBurden emissionsTrajectory localAmenity :
    ProjectView

observeProject : Observer → Project → ProjectView
observeProject operator aiDataCentre = computeCapacity
observeProject grid aiDataCentre = gridLoad
observeProject city aiDataCentre = infrastructureBurden
observeProject climate aiDataCentre = emissionsTrajectory
observeProject community aiDataCentre = localAmenity
observeProject _ housingProject = infrastructureBurden

------------------------------------------------------------------------
-- Legal approval, social legitimation, popularity and planning admissibility
-- are separate coordinates.  No one coordinate auto-promotes another.
------------------------------------------------------------------------

data LegalApprovalImpliesSocialLegitimationPermission : Set where

data PopularityImpliesLegalAdmissibilityPermission : Set where

legalApprovalDoesNotAutoPromoteToSocialLegitimation :
  LegalApprovalImpliesSocialLegitimationPermission → ⊥
legalApprovalDoesNotAutoPromoteToSocialLegitimation ()

popularityDoesNotAutoPromoteToLegalAdmissibility :
  PopularityImpliesLegalAdmissibilityPermission → ⊥
popularityDoesNotAutoPromoteToLegalAdmissibility ()

------------------------------------------------------------------------
-- Integrity architecture: corruption/capture is not represented as an
-- unsupported scalar.  Concrete cases must supply failures of explicit
-- process properties.
------------------------------------------------------------------------

record DecisionIntegrity : Set₁ where
  field
    Authority    : Set
    Evidence     : Set
    Rule         : Set
    AffectedParty : Set
    Benefit      : Set
    Cost         : Set

    ConflictFree       : Set
    PubliclyReviewable : Set
    ReasonsTraceable   : Set
    BenefitsDisclosed  : Set
    ProcedurePreserved : Set

open DecisionIntegrity public

record DistributedImpact : Set₁ where
  field
    Actor   : Set
    Benefit : Actor → Set
    Cost    : Actor → Set

open DistributedImpact public

data AggregateBenefitImpliesDistributiveLegitimacyPermission : Set where

aggregateBenefitDoesNotAutoPromoteToDistributiveLegitimacy :
  AggregateBenefitImpliesDistributiveLegitimacyPermission → ⊥
aggregateBenefitDoesNotAutoPromoteToDistributiveLegitimacy ()
