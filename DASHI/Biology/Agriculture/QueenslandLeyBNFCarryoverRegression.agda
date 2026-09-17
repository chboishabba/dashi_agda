module DASHI.Biology.Agriculture.QueenslandLeyBNFCarryoverRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.QueenslandLeyBNFCarryoverExact as Q

hossain1995DOIPinned : Q.hossainEtAl1995DOI ≡ "10.1071/AR9950493"
hossain1995DOIPinned = refl

hossain1996SoilDOIPinned : Q.hossainEtAl1996SoilDOI ≡ "10.1071/SR9960273"
hossain1996SoilDOIPinned = refl

hossain1996CropDOIPinned : Q.hossainEtAl1996CropDOI ≡ "10.1071/SR9960289"
hossain1996CropDOIPinned = refl

pu2001DOIPinned : Q.puEtAl2001DOI ≡ "10.1023/A:1014462305825"
pu2001DOIPinned = refl

peoples2017DOIPinned : Q.peoplesEtAl2017DOI ≡ "10.1071/CP16248"
peoples2017DOIPinned = refl

strong2006DOIPinned : Q.strongEtAl2006DOI ≡ "10.1071/EA05007"
strong2006DOIPinned = refl

fixedNNotMineralN :
  Q.fixedNitrogenQuantityImpliesSameMineralNitrogenAtCropSowing Q.canonicalQueenslandLeyBoundary ≡ false
fixedNNotMineralN = refl

mineralNNotCropUptake :
  Q.soilMineralNitrogenImpliesEquivalentCropNitrogenUptake Q.canonicalQueenslandLeyBoundary ≡ false
mineralNNotCropUptake = refl

uptakeNotYield :
  Q.cropNitrogenUptakeImpliesYieldBenefit Q.canonicalQueenslandLeyBoundary ≡ false
uptakeNotYield = refl

fixedNNotReplacement :
  Q.fixedNitrogenInputImpliesAvoidedMineralFertilizer Q.canonicalQueenslandLeyBoundary ≡ false
fixedNNotReplacement = refl

singleRateEquivalenceNotReplacement :
  Q.singleFertilizerRateYieldEquivalenceImpliesReplacementValue Q.canonicalQueenslandLeyBoundary ≡ false
singleRateEquivalenceNotReplacement = refl

waterContextRetained :
  Q.waterLimitationMayBeDroppedFromFollowingCropResponse Q.canonicalQueenslandLeyBoundary ≡ false
waterContextRetained = refl

lossesRetained :
  Q.denitrificationLeachingImmobilisationMayBeDropped Q.canonicalQueenslandLeyBoundary ≡ false
lossesRetained = refl

soilNSuppressionRetained :
  Q.startingMineralNitrogenMayBeDroppedFromBNF Q.canonicalQueenslandLeyBoundary ≡ false
soilNSuppressionRetained = refl

cropSeasonRetained :
  Q.cropIdentityAndSeasonMayBeDropped Q.canonicalQueenslandLeyBoundary ≡ false
cropSeasonRetained = refl

acaciaLadderNotClosed :
  Q.queenslandLeyEvidenceClosesAcaciaAvoidedMineralN Q.canonicalQueenslandLeyBoundary ≡ false
acaciaLadderNotClosed = refl
