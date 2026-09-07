module DASHI.Biology.Agriculture.Hungria2024HeadlineLineageWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.Agriculture.HungriaEconomicEmissionModel2023Exact as Model2023

------------------------------------------------------------------------
-- 2024 / 2025 HEADLINE LINEAGE WELD
--
-- Embrapa's 2025 World Food Prize news item attributes to Hungria estimates
-- for 2024 of approximately USD 25 billion saved through avoided N fertilizer
-- and >230 million tonnes CO2-e mitigated by use of the bacteria.
--
-- The 2023 peer-reviewed producer gives an explicit model family and 2019-2020
-- outputs of USD 15.2 billion and 183 million Mg CO2-e.  Similar quantities
-- and language do not prove that the 2024 headline was produced by a literal
-- rerun of exactly that model with updated inputs.  This module makes the
-- missing version transport explicit.
------------------------------------------------------------------------

data HeadlineValue : Set where
  savingsUSD25B : HeadlineValue
  mitigationCO2e230MtPlus : HeadlineValue

data LineageCoordinate : Set where
  modelEquationIdentity : LineageCoordinate
  cropScopeIdentity : LineageCoordinate
  season2024YieldInput : LineageCoordinate
  season2024AreaInput : LineageCoordinate
  season2024UreaPriceInput : LineageCoordinate
  season2024SecondaryNAssumption : LineageCoordinate
  season2024RecoveryAssumption : LineageCoordinate
  season2024EmissionCoefficient : LineageCoordinate
  calculationReplay : LineageCoordinate
  publicationAttribution : LineageCoordinate

data WeldStatus : Set where
  sourceBacked : WeldStatus
  openWeld : WeldStatus

weldStatus : LineageCoordinate → WeldStatus
weldStatus modelEquationIdentity = openWeld
weldStatus cropScopeIdentity = sourceBacked
weldStatus season2024YieldInput = openWeld
weldStatus season2024AreaInput = openWeld
weldStatus season2024UreaPriceInput = openWeld
weldStatus season2024SecondaryNAssumption = openWeld
weldStatus season2024RecoveryAssumption = openWeld
weldStatus season2024EmissionCoefficient = openWeld
weldStatus calculationReplay = openWeld
weldStatus publicationAttribution = sourceBacked

cropScopeIsBacked : weldStatus cropScopeIdentity ≡ sourceBacked
cropScopeIsBacked = refl

modelEquationIdentityStillOpen : weldStatus modelEquationIdentity ≡ openWeld
modelEquationIdentityStillOpen = refl

calculationReplayStillOpen : weldStatus calculationReplay ≡ openWeld
calculationReplayStillOpen = refl

------------------------------------------------------------------------
-- Version non-identity is already mechanically visible from the source-owned
-- integer outputs.
------------------------------------------------------------------------

paperValueNotHeadline25B :
  Model2023.avoidedUreaCostMillionUSD Model2023.paper2019_2020Outputs ≡ 25000 → ⊥
paperValueNotHeadline25B = Model2023.paper2023AvoidedCostEquals2025Headline25000

paperMitigationNotHeadline230 :
  Model2023.mitigatedCO2eMillionMg Model2023.paper2019_2020Outputs ≡ 230 → ⊥
paperMitigationNotHeadline230 = Model2023.paper2023MitigationEquals2025Headline230

------------------------------------------------------------------------
-- DASHI-original promotion boundary.
------------------------------------------------------------------------

record HeadlinePromotionBoundary : Set where
  constructor headlinePromotionBoundary
  field
    sameAuthorsOrInstitutionImpliesSameCalculation : Bool
    sameAuthorsOrInstitutionImpliesSameCalculationIsFalse :
      sameAuthorsOrInstitutionImpliesSameCalculation ≡ false
    similarModelOutputsImpliesSameInputVintage : Bool
    similarModelOutputsImpliesSameInputVintageIsFalse :
      similarModelOutputsImpliesSameInputVintage ≡ false
    laterInstitutionalNumberMayBeAccurate : Bool
    laterInstitutionalNumberMayBeAccurateIsTrue :
      laterInstitutionalNumberMayBeAccurate ≡ true
    laterInstitutionalNumberAlreadyReplayed : Bool
    laterInstitutionalNumberAlreadyReplayedIsFalse :
      laterInstitutionalNumberAlreadyReplayed ≡ false

canonicalHeadlinePromotionBoundary : HeadlinePromotionBoundary
canonicalHeadlinePromotionBoundary =
  headlinePromotionBoundary false refl false refl true refl false refl
