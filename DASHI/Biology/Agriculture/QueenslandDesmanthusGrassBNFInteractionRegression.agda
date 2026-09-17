module DASHI.Biology.Agriculture.QueenslandDesmanthusGrassBNFInteractionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.QueenslandDesmanthusGrassBNFInteractionExact as D

inoculationNotOccupancy :
  D.inoculationImpliesHighInoculantNoduleOccupancy D.canonicalDesmanthusBoundary ≡ false
inoculationNotOccupancy = refl

occupancyNotNdfa :
  D.highInoculantNoduleOccupancyImpliesHighNdfa D.canonicalDesmanthusBoundary ≡ false
occupancyNotNdfa = refl

soilNRetained :
  D.soilMineralNitrogenMayBeDroppedFromRealisedFixation D.canonicalDesmanthusBoundary ≡ false
soilNRetained = refl

indigenousRhizobiaRetained :
  D.indigenousRhizobialPopulationMayBeDropped D.canonicalDesmanthusBoundary ≡ false
indigenousRhizobiaRetained = refl

droughtNoduleTurnoverRetained :
  D.droughtAndNoduleTurnoverMayBeDropped D.canonicalDesmanthusBoundary ≡ false
droughtNoduleTurnoverRetained = refl

companionGrassNotPurelyNegative :
  D.companionGrassEffectIsUniversallyNegative D.canonicalDesmanthusBoundary ≡ false
companionGrassNotPurelyNegative = refl

pureSwardNotUniversal :
  D.pureSwardFixationPredictsGrassMixtureFixation D.canonicalDesmanthusBoundary ≡ false
pureSwardNotUniversal = refl

fieldNotPotIdentity :
  D.potResponseCreatesFieldSameObjectReceipt D.canonicalDesmanthusBoundary ≡ false
fieldNotPotIdentity = refl

acaciaNotClosed :
  D.desmanthusEvidenceClosesAcaciaReactionEnablement D.canonicalDesmanthusBoundary ≡ false
acaciaNotClosed = refl
