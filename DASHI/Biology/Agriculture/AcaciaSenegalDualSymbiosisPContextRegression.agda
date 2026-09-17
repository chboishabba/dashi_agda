module DASHI.Biology.Agriculture.AcaciaSenegalDualSymbiosisPContextRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalDualSymbiosisPContextExact as S

colonna1991DOIPinned : S.colonnaEtAl1991DOI ≡ "10.1007/BF00205900"
colonna1991DOIPinned = refl

yonli2022DOIPinned : S.yonliEtAl2022DOI ≡ "10.3389/fenvs.2022.803009"
yonli2022DOIPinned = refl

rhizobialIdentityAloneIsNotRealisedPerformance :
  S.rhizobialIdentityAloneAdequateForRealisedPerformance S.canonicalDualSymbiosisBoundary ≡ false
rhizobialIdentityAloneIsNotRealisedPerformance = refl

availablePContextCannotBeCollapsed :
  S.availablePContextMayBeCollapsedToTotalP S.canonicalDualSymbiosisBoundary ≡ false
availablePContextCannotBeCollapsed = refl

nurseryBiomassDoesNotDetermineFieldSurvival :
  S.nurseryBiomassImpliesFieldSurvival S.canonicalDualSymbiosisBoundary ≡ false
nurseryBiomassDoesNotDetermineFieldSurvival = refl

higherNutrientAmendmentDoesNotGuaranteeBetterSymbiosis :
  S.higherNutrientAmendmentImpliesBetterSymbiosis S.canonicalDualSymbiosisBoundary ≡ false
higherNutrientAmendmentDoesNotGuaranteeBetterSymbiosis = refl

symbiosisStateMustRetainBothPartnerClasses :
  S.amfAndRhizobialStateMustRemainIndexed S.canonicalDualSymbiosisBoundary ≡ true
symbiosisStateMustRetainBothPartnerClasses = refl

greenhouseAndMineRestorationAreNotSameEmpiricalObject :
  S.greenhouseAndMineRestorationCreateSameEmpiricalObject S.canonicalDualSymbiosisBoundary ≡ false
greenhouseAndMineRestorationAreNotSameEmpiricalObject = refl
