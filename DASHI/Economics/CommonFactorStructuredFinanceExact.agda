module DASHI.Economics.CommonFactorStructuredFinanceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- GENERIC STRUCTURED-FINANCE / COMMON-FACTOR CALCULUS
--
-- Separate project/SPV multiplicity from independence of ultimate economic
-- drivers.  This is intentionally analogous to provenance independence:
-- different documentary or legal wrappers do not manufacture independent
-- upstream causes.
------------------------------------------------------------------------

record StructuredFinanceSystem : Set₁ where
  field
    Project Driver Instrument RatingAgency : Set
    UltimateEconomicDriver : Project → Driver
    Backs : Instrument → Project → Set
    Rates : RatingAgency → Instrument → Set
    EconomicDependence : RatingAgency → Project → Set

open StructuredFinanceSystem public

record SharedUltimateDriver
    (sys : StructuredFinanceSystem)
    (left right : Project sys) : Set where
  field
    sameDriver : UltimateEconomicDriver sys left ≡ UltimateEconomicDriver sys right

record ValidatorConflictExposure
    (sys : StructuredFinanceSystem)
    (validator : RatingAgency sys)
    (project : Project sys) : Set where
  field
    economicallyDependent : EconomicDependence sys validator project

-- Actual bias/invalidity is a distinct promotion and requires its own receipt.
record ActualValidatorBias : Set₁ where
  field
    EvidenceOfBias : Set
    evidence       : EvidenceOfBias

open ActualValidatorBias public

data ProjectMultiplicityImpliesRiskIndependencePermission : Set where

data ValidatorDependenceImpliesInvalidRatingPermission : Set where

data ConflictExposureImpliesActualBiasPermission : Set where

projectMultiplicityDoesNotAutoPromoteToRiskIndependence :
  ProjectMultiplicityImpliesRiskIndependencePermission → ⊥
projectMultiplicityDoesNotAutoPromoteToRiskIndependence ()

validatorDependenceDoesNotAutoPromoteToInvalidRating :
  ValidatorDependenceImpliesInvalidRatingPermission → ⊥
validatorDependenceDoesNotAutoPromoteToInvalidRating ()

conflictExposureDoesNotAutoPromoteToActualBias :
  ConflictExposureImpliesActualBiasPermission → ⊥
conflictExposureDoesNotAutoPromoteToActualBias ()
