module DASHI.Culture.ColonialPerformanceStatusNonfactorabilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- PERFORMANCE / STATUS / ENDORSEMENT NON-COLLAPSE
--
-- These are finite DASHI countermodels calibrated by the Powers problem-space.
-- They do not assert the legal status, beliefs or intentions of any named
-- historical performer.
------------------------------------------------------------------------

data PerformanceStatusState : Set where
  sameRoleRestrictedOccupancy : PerformanceStatusState
  sameRoleOpenOccupancy : PerformanceStatusState

data PerformedRole : Set where
  eliteStageRole : PerformedRole

data SocialOccupancy : Set where
  sociallyRestricted : SocialOccupancy
  sociallyOpen : SocialOccupancy

performedRole : PerformanceStatusState → PerformedRole
performedRole _ = eliteStageRole

socialOccupancy : PerformanceStatusState → SocialOccupancy
socialOccupancy sameRoleRestrictedOccupancy = sociallyRestricted
socialOccupancy sameRoleOpenOccupancy = sociallyOpen

samePerformedRole :
  performedRole sameRoleRestrictedOccupancy
  ≡ performedRole sameRoleOpenOccupancy
samePerformedRole = refl

socialOccupancyDiffers :
  socialOccupancy sameRoleRestrictedOccupancy
  ≡ socialOccupancy sameRoleOpenOccupancy → ⊥
socialOccupancyDiffers ()

performedRoleCannotRecoverSocialOccupancy :
  INF.FactorsThrough performedRole socialOccupancy → ⊥
performedRoleCannotRecoverSocialOccupancy =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameRoleRestrictedOccupancy
      sameRoleOpenOccupancy
      samePerformedRole
      socialOccupancyDiffers)

------------------------------------------------------------------------
-- Participation in a represented work does not determine endorsement.
------------------------------------------------------------------------

data PerformanceBeliefState : Set where
  performsWithoutEndorsement : PerformanceBeliefState
  performsWithEndorsement : PerformanceBeliefState

data PerformanceSurface : Set where
  samePerformance : PerformanceSurface

data Endorsement : Set where
  endorsementAbsent : Endorsement
  endorsementPresent : Endorsement

performanceSurface : PerformanceBeliefState → PerformanceSurface
performanceSurface _ = samePerformance

endorsement : PerformanceBeliefState → Endorsement
endorsement performsWithoutEndorsement = endorsementAbsent
endorsement performsWithEndorsement = endorsementPresent

endorsementDiffers :
  endorsement performsWithoutEndorsement
  ≡ endorsement performsWithEndorsement → ⊥
endorsementDiffers ()

performanceCannotRecoverEndorsement :
  INF.FactorsThrough performanceSurface endorsement → ⊥
performanceCannotRecoverEndorsement =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      performsWithoutEndorsement
      performsWithEndorsement
      refl
      endorsementDiffers)

record ColonialPerformanceStatusBoundary : Set where
  constructor colonial-performance-status-boundary
  field
    stageRoleDeterminesLegalSocialStatus : Bool
    stageRoleDeterminesLegalSocialStatusIsFalse :
      stageRoleDeterminesLegalSocialStatus ≡ false
    performanceDeterminesBelief : Bool
    performanceDeterminesBeliefIsFalse : performanceDeterminesBelief ≡ false
    finiteWitnessIsNamedHistoricalBiography : Bool
    finiteWitnessIsNamedHistoricalBiographyIsFalse :
      finiteWitnessIsNamedHistoricalBiography ≡ false

canonicalColonialPerformanceStatusBoundary : ColonialPerformanceStatusBoundary
canonicalColonialPerformanceStatusBoundary =
  colonial-performance-status-boundary false refl false refl false refl
