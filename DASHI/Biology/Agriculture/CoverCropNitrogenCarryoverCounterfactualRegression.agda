module DASHI.Biology.Agriculture.CoverCropNitrogenCarryoverCounterfactualRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.CoverCropNitrogenCarryoverCounterfactualExact as C

fontesEtAl2017DOIPinned :
  C.fontesEtAl2017DOI ≡ "10.2134/agronj2017.03.0180"
fontesEtAl2017DOIPinned = refl

besanconEtAl2021DOIPinned :
  C.besanconEtAl2021DOI ≡ "10.21273/HORTTECH04811-21"
besanconEtAl2021DOIPinned = refl

dorissantEtAl2022DOIPinned :
  C.dorissantEtAl2022DOI ≡ "10.1002/agg2.20311"
dorissantEtAl2022DOIPinned = refl

residueNIsNotCropAvailableN :
  C.residueNReleaseImpliesCropAvailableNAtDemandTime C.canonicalCarryoverBoundary ≡ false
residueNIsNotCropAvailableN = refl

legumeIdentityDoesNotQuantifyReplacement :
  C.legumePredecessorIdentityImpliesQuantifiedFertilizerReplacement C.canonicalCarryoverBoundary ≡ false
legumeIdentityDoesNotQuantifyReplacement = refl

explicitNResponseCurveIsRequired :
  C.explicitMineralNRateCounterfactualRequiredForReplacementValue C.canonicalCarryoverBoundary ≡ true
explicitNResponseCurveIsRequired = refl

sudangrassDoesNotCreateBNF :
  C.sorghumSudangrassResidueNImpliesBiologicalNFixation C.canonicalCarryoverBoundary ≡ false
sudangrassDoesNotCreateBNF = refl

annualCoverResultDoesNotPayAcacia :
  C.annualCoverCropReplacementValueClosesAcaciaAvoidedMineralN C.canonicalCarryoverBoundary ≡ false
annualCoverResultDoesNotPayAcacia = refl
