module DASHI.Governance.TrumpEnergyCrackSpreadBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- THIN TRUMP-ENERGY / CRACK-SPREAD BOUNDARY
--
-- This module is intentionally self-contained and dependency-light.
-- It exposes the energy crack-spread boundary without importing
-- psychogeography, energy macro models, or external market cascades.
------------------------------------------------------------------------

record TrumpEnergyCrackSpreadBoundary : Set where
  constructor trump-energy-crack-spread-boundary
  field
    crudePriceEqualsRetailFuelBurden : Bool
    crudePriceEqualsRetailFuelBurdenIsFalse : crudePriceEqualsRetailFuelBurden ≡ false
    crudeSupplyAdequacyGuaranteesCheapProducts : Bool
    crudeSupplyAdequacyGuaranteesCheapProductsIsFalse :
      crudeSupplyAdequacyGuaranteesCheapProducts ≡ false
    highRefiningMarginImpliesConsumerBenefit : Bool
    highRefiningMarginImpliesConsumerBenefitIsFalse : highRefiningMarginImpliesConsumerBenefit ≡ false
    energyAbundanceNarrativeDeterminesMaterialBenefit : Bool
    energyAbundanceNarrativeDeterminesMaterialBenefitIsFalse :
      energyAbundanceNarrativeDeterminesMaterialBenefit ≡ false
    tariffPolicyUniquelyCausesCurrentCrackSpread : Bool
    tariffPolicyUniquelyCausesCurrentCrackSpreadIsFalse :
      tariffPolicyUniquelyCausesCurrentCrackSpread ≡ false
    militaryEscalationUniquelyCausesCurrentCrackSpread : Bool
    militaryEscalationUniquelyCausesCurrentCrackSpreadIsFalse :
      militaryEscalationUniquelyCausesCurrentCrackSpread ≡ false
    dailySnapshotProvesStructuralTrend : Bool
    dailySnapshotProvesStructuralTrendIsFalse : dailySnapshotProvesStructuralTrend ≡ false
    namedActorMotiveFollowsFromMarketOutcome : Bool
    namedActorMotiveFollowsFromMarketOutcomeIsFalse :
      namedActorMotiveFollowsFromMarketOutcome ≡ false
    reading : String

open TrumpEnergyCrackSpreadBoundary public

canonicalTrumpEnergyCrackSpreadBoundary : TrumpEnergyCrackSpreadBoundary
canonicalTrumpEnergyCrackSpreadBoundary =
  trump-energy-crack-spread-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Current oil/refining conditions are a multi-fibre political-economy assay: crude price, refinery margin, retail burden, upstream/refiner/consumer position, trade policy and geopolitical risk remain distinct. Trump-policy and populist/plutocratic owners may structure the questions, but current spreads do not by themselves establish named-actor motive, unique causation, worker benefit or consumer benefit."
