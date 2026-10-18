module DASHI.Environment.FloatingSolarBiofoulingLESValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.FloatingSolarBiofoulingLESExact as Solar

------------------------------------------------------------------------
-- RED-first regression owner.
------------------------------------------------------------------------

sourceDoiIsPinned : Solar.mavrakiEtAl2025DOI ≡ "10.1016/j.seares.2025.102627"
sourceDoiIsPinned = refl

observedTaxaArePinned : Solar.mavrakiObservedTaxa ≡ 47
observedTaxaArePinned = refl

observedNISTaxaArePinned : Solar.mavrakiObservedNISTaxa ≡ 12
observedNISTaxaArePinned = refl

substrateAloneCannotDetermineReefEstablishment :
  Solar.SubstrateFactorisation → ⊥
substrateAloneCannotDetermineReefEstablishment =
  Solar.substrateAloneCannotDetermineReefEstablishment

larvalSupplyAloneCannotDetermineReefEstablishment :
  Solar.LarvalSupplyFactorisation → ⊥
larvalSupplyAloneCannotDetermineReefEstablishment =
  Solar.larvalSupplyAloneCannotDetermineReefEstablishment

filtrationAloneCannotDetermineNetWaterQualityBenefit :
  Solar.FiltrationFactorisation → ⊥
filtrationAloneCannotDetermineNetWaterQualityBenefit =
  Solar.filtrationAloneCannotDetermineNetWaterQualityBenefit

colonisationDoesNotCreateNetBenefit :
  Solar.ColonisationImpliesNetEcologicalBenefit → ⊥
colonisationDoesNotCreateNetBenefit = Solar.colonisationDoesNotCreateNetBenefit

localRichnessDoesNotCreateWholeSystemValue :
  Solar.LocalTaxonRichnessImpliesWholeSystemValue → ⊥
localRichnessDoesNotCreateWholeSystemValue =
  Solar.localRichnessDoesNotCreateWholeSystemValue

commercialScalingDoesNotFollowFromDemonstrator :
  Solar.DemonstratorImpliesCommercialScaleOutcome → ⊥
commercialScalingDoesNotFollowFromDemonstrator =
  Solar.demonstratorDoesNotCreateCommercialScaleOutcome

harvestExportIsDistinctFromFiltration :
  Solar.FiltrationEqualsNetNutrientExport → ⊥
harvestExportIsDistinctFromFiltration = Solar.filtrationDoesNotEqualNetNutrientExport

habitatProvisionIsNotAutomaticallyBenignConnectivity :
  Solar.HabitatProvisionImpliesBenignConnectivity → ⊥
habitatProvisionIsNotAutomaticallyBenignConnectivity =
  Solar.habitatProvisionDoesNotCreateBenignConnectivity

seedingDoesNotCreateSelfSustainingReef :
  Solar.SeedingImpliesSelfSustainingReef → ⊥
seedingDoesNotCreateSelfSustainingReef =
  Solar.seedingDoesNotCreateSelfSustainingReef
