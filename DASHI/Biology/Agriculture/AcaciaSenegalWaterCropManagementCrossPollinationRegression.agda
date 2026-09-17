module DASHI.Biology.Agriculture.AcaciaSenegalWaterCropManagementCrossPollinationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalWaterCropManagementCrossPollinationExact as W

raddad2007DOIPinned : W.raddadLuukkanen2007DOI ≡ "10.1016/j.agwat.2006.06.001"
raddad2007DOIPinned = refl

gaafar2006DOIPinned : W.gaafarEtAl2006DOI ≡ "10.1007/s10457-005-2918-y"
gaafar2006DOIPinned = refl

speciesAndDensityDoNotDetermineWaterCompetition :
  W.speciesAndDensityDetermineWaterCompetition W.canonicalWaterCropBoundary ≡ false
speciesAndDensityDoNotDetermineWaterCompetition = refl

waterResponseKeepsSoilContext :
  W.soilHydraulicContextMustRemainIndexed W.canonicalWaterCropBoundary ≡ true
waterResponseKeepsSoilContext = refl

earlyStageResultDoesNotUniversaliseAcrossAge :
  W.earlyStageNoYieldPenaltyImpliesMatureSystemNoYieldPenalty W.canonicalWaterCropBoundary ≡ false
earlyStageResultDoesNotUniversaliseAcrossAge = refl

cropYieldDoesNotIdentifyWaterMechanism :
  W.cropYieldAloneIdentifiesWaterCompetitionMechanism W.canonicalWaterCropBoundary ≡ false
cropYieldDoesNotIdentifyWaterMechanism = refl
