module DASHI.Biology.Agriculture.AcaciaSenegalFixedNTransferNutrientBudgetRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.AcaciaSenegalFixedNTransferNutrientBudgetExact as T

isaac2012DOIPinned : T.isaacHinsingerHarmand2012DOI ≡ "10.1016/j.scitotenv.2011.12.071"
isaac2012DOIPinned = refl

isaac2012PMIDPinned : T.isaacHinsingerHarmand2012PMID ≡ "22446108"
isaac2012PMIDPinned = refl

raddad2006DOIPinned : T.raddadEtAl2006DOI ≡ "10.1007/s10457-006-9009-6"
raddad2006DOIPinned = refl

deans1999DOIPinned : T.deansEtAl1999DOI ≡ "10.1016/S0378-1127(99)00063-8"
deans1999DOIPinned = refl

fall2012DOIPinned : T.fallEtAl2012DOI ≡ "10.1016/j.jenvman.2011.03.038"
fall2012DOIPinned = refl

fall2012PMIDPinned : T.fallEtAl2012PMID ≡ "21514716"
fall2012PMIDPinned = refl

elTahir2009DOIPinned : T.elTahirEtAl2009DOI ≡ "10.1016/j.jaridenv.2008.11.007"
elTahir2009DOIPinned = refl

basga2018DOIPinned : T.basgaEtAl2018DOI ≡ "10.5897/AJAR2018.13283"
basga2018DOIPinned = refl

gerakis1970DOIPinned : T.gerakisTsangarakis1970DOI ≡ "10.1007/BF01378198"
gerakis1970DOIPinned = refl

elTahir2013NoDOIInvented :
  Attribution.doiState T.elTahirDaldoumArdo2013 ≡ Attribution.noDOIRecordedByAtlas
elTahir2013NoDOIInvented = refl

plantFixedNDoesNotCreateInterplantTransfer :
  T.plantFixedNContributionImpliesInterplantTransfer T.canonicalTransferBudgetBoundary ≡ false
plantFixedNDoesNotCreateInterplantTransfer = refl

transferIsContextIndexed :
  T.transferMustRemainRootContactPAndTimeIndexed T.canonicalTransferBudgetBoundary ≡ true
transferIsContextIndexed = refl

interplantTransferDoesNotCreatePositiveFieldBalance :
  T.interplantTransferImpliesPositiveFieldNBalance T.canonicalTransferBudgetBoundary ≡ false
interplantTransferDoesNotCreatePositiveFieldBalance = refl

positiveBalanceDoesNotCreateFertilizerSubstitution :
  T.positiveNBalanceImpliesFertilizerSubstitution T.canonicalTransferBudgetBoundary ≡ false
positiveBalanceDoesNotCreateFertilizerSubstitution = refl

abovegroundOnlyBudgetIsNotWholeSystemBudget :
  T.abovegroundBudgetEqualsWholeSystemNBalance T.canonicalTransferBudgetBoundary ≡ false
abovegroundOnlyBudgetIsNotWholeSystemBudget = refl

soilMineralNObserverGeometryCannotBeDropped :
  T.soilMineralNObserverGeometryMayBeDropped T.canonicalTransferBudgetBoundary ≡ false
soilMineralNObserverGeometryCannotBeDropped = refl

priorAccumulationDoesNotGuaranteePersistenceAfterConversion :
  T.priorNutrientAccumulationImpliesPersistentPostConversionStock T.canonicalTransferBudgetBoundary ≡ false
priorAccumulationDoesNotGuaranteePersistenceAfterConversion = refl

managementHistoryRemainsIndexed :
  T.landUseTransitionAndHistoryMustRemainIndexed T.canonicalTransferBudgetBoundary ≡ true
managementHistoryRemainsIndexed = refl

formerTreePatchMemoryCannotBeDropped :
  T.clearedLandCoverImpliesSpatiallyHomogeneousSoil T.canonicalTransferBudgetBoundary ≡ false
formerTreePatchMemoryCannotBeDropped = refl

priorTreePatchLocationRemainsIndexed :
  T.formerTreePatchLocationMustRemainIndexed T.canonicalTransferBudgetBoundary ≡ true
priorTreePatchLocationRemainsIndexed = refl

cropYieldWithMineralNDoesNotPayAvoidedMineralN :
  T.cropYieldUnderCoAppliedMineralNClosesAvoidedMineralN T.canonicalTransferBudgetBoundary ≡ false
cropYieldWithMineralNDoesNotPayAvoidedMineralN = refl

fertilizerCotreatmentRemainsIndexed :
  T.mineralFertilizerCotreatmentMustRemainIndexed T.canonicalTransferBudgetBoundary ≡ true
fertilizerCotreatmentRemainsIndexed = refl

managementExportRemainsIndexed :
  T.harvestAndExportMustRemainIndexed T.canonicalTransferBudgetBoundary ≡ true
managementExportRemainsIndexed = refl

noFertilizerApplicationNotSubstitutionCounterfactual :
  T.noMineralFertilizerAppliedImpliesMeasuredFertilizerSubstitution T.canonicalTransferBudgetBoundary ≡ false
noFertilizerApplicationNotSubstitutionCounterfactual = refl

modelledBNFNotObservedFlux :
  T.modelledBNFFractionImpliesObservedFixedNFlux T.canonicalTransferBudgetBoundary ≡ false
modelledBNFNotObservedFlux = refl

seasonalBudgetNotCropDemand :
  T.seasonalNutrientBalanceEqualsSeasonalCropNDemand T.canonicalTransferBudgetBoundary ≡ false
seasonalBudgetNotCropDemand = refl

seasonCropSystemRetained :
  T.cropSpeciesTreeDensityAndSeasonMustRemainIndexed T.canonicalTransferBudgetBoundary ≡ true
seasonCropSystemRetained = refl
