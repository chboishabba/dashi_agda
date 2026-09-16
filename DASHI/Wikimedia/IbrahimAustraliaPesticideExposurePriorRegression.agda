module DASHI.Wikimedia.IbrahimAustraliaPesticideExposurePriorRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RED surface for Australian pesticide exposure-prior governance.
--
-- Required distinctions:
--   legal label use != permanently safe under changed consumption;
--   non-food quarantine treatment != food-residue admission;
--   permit persistence != consumer ingestion safety;
--   country-level ranking requires a common comparison basis.
------------------------------------------------------------------------

record AustraliaExposurePriorRegression : Set where
  constructor australia-exposure-prior-regression
  field
    berryConsumptionShiftTyped : Bool
    dimethoateLabelRevisionTyped : Bool
    childAcuteReferenceDoseTyped : Bool
    fireAntPotDipTyped : Bool
    persistentBifenthrinMediaTyped : Bool
    foodVsNonFoodBoundaryTyped : Bool
    staleExposurePriorFirewallTyped : Bool
    countryRankingFirewallTyped : Bool
open AustraliaExposurePriorRegression public

requiredAustraliaExposurePriorRegression : AustraliaExposurePriorRegression
requiredAustraliaExposurePriorRegression =
  australia-exposure-prior-regression
    true true true true true true true true
