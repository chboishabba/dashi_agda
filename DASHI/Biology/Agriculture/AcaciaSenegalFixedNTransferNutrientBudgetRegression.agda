module DASHI.Biology.Agriculture.AcaciaSenegalFixedNTransferNutrientBudgetRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalFixedNTransferNutrientBudgetExact as T

isaac2012DOIPinned : T.isaacHinsingerHarmand2012DOI ≡ "10.1016/j.scitotenv.2011.12.071"
isaac2012DOIPinned = refl

isaac2012PMIDPinned : T.isaacHinsingerHarmand2012PMID ≡ "22446108"
isaac2012PMIDPinned = refl

raddad2006DOIPinned : T.raddadEtAl2006DOI ≡ "10.1007/s10457-006-9009-6"
raddad2006DOIPinned = refl

deans1999DOIPinned : T.deansEtAl1999DOI ≡ "10.1016/S0378-1127(99)00063-8"
deans1999DOIPinned = refl

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

managementExportRemainsIndexed :
  T.harvestAndExportMustRemainIndexed T.canonicalTransferBudgetBoundary ≡ true
managementExportRemainsIndexed = refl
