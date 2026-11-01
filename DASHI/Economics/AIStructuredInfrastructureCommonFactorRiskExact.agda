module DASHI.Economics.AIStructuredInfrastructureCommonFactorRiskExact where

open import DASHI.Core.Prelude
import DASHI.Economics.CommonFactorStructuredFinanceExact as Structured

------------------------------------------------------------------------
-- AI INFRASTRUCTURE STRUCTURED-FINANCE SPECIALISATION
------------------------------------------------------------------------

record AIInfrastructureStructuredFinance : Set₁ where
  field
    structuredSystem : Structured.StructuredFinanceSystem

open AIInfrastructureStructuredFinance public

record MonetisableAcceleratorDemandCommonFactor
    (sys : AIInfrastructureStructuredFinance)
    (left right : Structured.Project (structuredSystem sys)) : Set where
  field
    sharedDriver : Structured.SharedUltimateDriver (structuredSystem sys) left right

-- Multiple legal projects/SPVs/instruments can still be one economic bet if
-- their ultimate driver is shared.  No claim about a named securitisation is
-- promoted here without a source-backed application receipt.
projectMultiplicityDoesNotCloseRiskIndependence :
  Structured.ProjectMultiplicityImpliesRiskIndependencePermission → ⊥
projectMultiplicityDoesNotCloseRiskIndependence =
  Structured.projectMultiplicityDoesNotAutoPromoteToRiskIndependence

validatorDependenceDoesNotCloseInvalidity :
  Structured.ValidatorDependenceImpliesInvalidRatingPermission → ⊥
validatorDependenceDoesNotCloseInvalidity =
  Structured.validatorDependenceDoesNotAutoPromoteToInvalidRating

conflictExposureDoesNotCloseBias :
  Structured.ConflictExposureImpliesActualBiasPermission → ⊥
conflictExposureDoesNotCloseBias =
  Structured.conflictExposureDoesNotAutoPromoteToActualBias
