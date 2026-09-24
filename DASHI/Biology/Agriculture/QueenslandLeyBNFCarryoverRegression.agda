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

dalal2004DurationDOIPinned : Q.dalalEtAl2004DurationDOI ≡ "10.1071/EA03166"
dalal2004DurationDOIPinned = refl

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

soilNImprovementDoesNotMeanWaterRecovery :
  Q.soilNitrogenImprovementImpliesRecoveredSoilWater Q.canonicalQueenslandLeyBoundary ≡ false
soilNImprovementDoesNotMeanWaterRecovery = refl

longerLeyNotMonotoneCropBenefit :
  Q.longerLeyDurationImpliesMonotoneFollowingCropBenefit Q.canonicalQueenslandLeyBoundary ≡ false
longerLeyNotMonotoneCropBenefit = refl

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


constructiveTransportMathOwned :
  Q.constructiveTransportKernelMathOwned Q.canonicalQueenslandLeyBoundary ≡ true
constructiveTransportMathOwned = refl

empiricalKernelBoundStillOpen :
  Q.empiricalPolynomialGeometricKernelBoundOwned Q.canonicalQueenslandLeyBoundary ≡ false
empiricalKernelBoundStillOpen = refl

finiteObservationNotAsymptoticStabilisation :
  Q.finiteObservationImpliesAsymptoticStabilisation Q.canonicalQueenslandLeyBoundary ≡ false
finiteObservationNotAsymptoticStabilisation = refl


firstOrderResidueKineticsSourceOwned :
  Q.firstOrderResidueKineticsSourceOwned
    Q.canonicalQueenslandLeyBoundary ≡ true
firstOrderResidueKineticsSourceOwned = refl

kineticsDoesNotDirectlySupplyBishopKernel :
  Q.firstOrderKineticsDirectlySuppliesDiscreteBishopKernel
    Q.canonicalQueenslandLeyBoundary ≡ false
kineticsDoesNotDirectlySupplyBishopKernel = refl


firstOrderDiscreteCompilerOwned :
  Q.firstOrderRateToDiscreteContractionCompilerOwned
    Q.canonicalQueenslandLeyBoundary ≡ true
firstOrderDiscreteCompilerOwned = refl

selectedRateStepStillOpen :
  Q.selectedEmpiricalRateTimeStepEmbeddedForAsymptoticUse
    Q.canonicalQueenslandLeyBoundary ≡ false
selectedRateStepStillOpen = refl

routeFallowRecoveryJoinOwned :
  Q.queenslandRouteFallowRecoveryJoinOwned
    Q.canonicalQueenslandLeyBoundary ≡ true
routeFallowRecoveryJoinOwned = refl

grdcJoinNotReplacementCurve :
  Q.routeFallowRecoveryJoinCreatesMineralNResponseCurve
    Q.canonicalQueenslandLeyBoundary ≡ false
grdcJoinNotReplacementCurve = refl


queenslandMultiRateResponseCurveOwned :
  Q.queenslandMultiRateFertilizerResponseCurveOwned
    Q.canonicalQueenslandLeyBoundary ≡ true
queenslandMultiRateResponseCurveOwned = refl

queenslandEquivalentStillNotAcacia :
  Q.queenslandChickpeaEquivalentClosesAcaciaAvoidedMineralN
    Q.canonicalQueenslandLeyBoundary ≡ false
queenslandEquivalentStillNotAcacia = refl

seasonEstimabilityMustRemain :
  Q.fertilizerEquivalentSeasonEstimabilityMayBeDropped
    Q.canonicalQueenslandLeyBoundary ≡ false
seasonEstimabilityMustRemain = refl
