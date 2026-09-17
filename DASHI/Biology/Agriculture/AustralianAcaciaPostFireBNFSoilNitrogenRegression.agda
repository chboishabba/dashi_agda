module DASHI.Biology.Agriculture.AustralianAcaciaPostFireBNFSoilNitrogenRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianAcaciaPostFireBNFSoilNitrogenExact as P

li2024DOIPinned :
  P.liEtAl2024DOI ≡ "10.1007/s11368-024-03816-8"
li2024DOIPinned = refl

nDfaNotFlux :
  P.foliarNdfaImpliesMeasuredFixedNFlux P.canonicalPostFireBNFBoundary ≡ false
nDfaNotFlux = refl

soilNNotBNFAlone :
  P.soilMineralNChangeAttributableToBNFAlone P.canonicalPostFireBNFBoundary ≡ false
soilNNotBNFAlone = refl

biocharGrowthNotBNF :
  P.biocharGrowthResponseImpliesBNFIncrease P.canonicalPostFireBNFBoundary ≡ false
biocharGrowthNotBNF = refl

fireHistoryRetained :
  P.prescribedFireHistoryMayBeDropped P.canonicalPostFireBNFBoundary ≡ false
fireHistoryRetained = refl

nDepositionRetained :
  P.atmosphericNitrogenDepositionMayBeDropped P.canonicalPostFireBNFBoundary ≡ false
nDepositionRetained = refl

rainfallRetained :
  P.extremeRainfallAndSoilMoistureMayBeDropped P.canonicalPostFireBNFBoundary ≡ false
rainfallRetained = refl

speciesRetained :
  P.acaciaSpeciesIdentityMayBeDropped P.canonicalPostFireBNFBoundary ≡ false
speciesRetained = refl

soilRetentionNotDemand :
  P.mineralNitrogenRetentionImpliesSeasonalPlantDemandPaid P.canonicalPostFireBNFBoundary ≡ false
soilRetentionNotDemand = refl

senegaliaLadderNotClosed :
  P.australianAcaciaEvidenceClosesSenegaliaBacterialFixedNFlux P.canonicalPostFireBNFBoundary ≡ false
senegaliaLadderNotClosed = refl
