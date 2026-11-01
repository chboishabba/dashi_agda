module DASHI.Biology.Agriculture.AustralianNativeLegumeRhizobiaRestorationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianNativeLegumeRhizobiaRestorationExact as A

burdon1999Pinned : A.burdon1999DOI ≡ "10.1046/j.1365-2664.1999.00409.x"
burdon1999Pinned = refl

thrall2000Pinned : A.thrall2000DOI ≡ "10.1046/j.1365-2664.2000.00470.x"
thrall2000Pinned = refl

murray2001Pinned : A.murray2001DOI ≡ "10.1046/j.1442-8903.2001.00086.x"
murray2001Pinned = refl

thrall2005Pinned : A.thrall2005DOI ≡ "10.1111/j.1365-2664.2005.01058.x"
thrall2005Pinned = refl

strainIdentityNotEnough : A.strainIdentityAloneDeterminesEffectiveSymbiosis A.canonicalAustralianRhizobiaBoundary ≡ false
strainIdentityNotEnough = refl

inoculationNotSurvival : A.inoculationImpliesFieldSurvival A.canonicalAustralianRhizobiaBoundary ≡ false
inoculationNotSurvival = refl

earlyGrowthNotCommunityRecovery : A.earlyGrowthImpliesCommunityRecovery A.canonicalAustralianRhizobiaBoundary ≡ false
earlyGrowthNotCommunityRecovery = refl

hostSiteContextRetained : A.hostSpeciesPopulationAndSiteMustRemainIndexed A.canonicalAustralianRhizobiaBoundary ≡ true
hostSiteContextRetained = refl
