module DASHI.Biology.Agriculture.AcaciaSenegalBNFMeasurementHierarchyRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalBNFMeasurementHierarchyExact as M

bakhoumDOIPinned : M.bakhoum2015DOI ≡ "10.1007/s00248-014-0507-1"
bakhoumDOIPinned = refl

githaeDOIPinned : M.githae2013DOI ≡ "10.1080/15324982.2013.784377"
githaeDOIPinned = refl

assefaKleinerDOIPinned : M.assefaKleiner1998DOI ≡ "10.1007/s003740050400"
assefaKleinerDOIPinned = refl

araNotDirectN2Rate :
  M.araEqualsDirectN2FixationRate M.canonicalMeasurementBoundary ≡ false
araNotDirectN2Rate = refl

araDoesNotDeterminePlantN :
  M.araDeterminesPlantNitrogenContent M.canonicalMeasurementBoundary ≡ false
araDoesNotDeterminePlantN = refl

saraNotPlantDelivery :
  M.saraEqualsIntegratedPlantFixedNDelivery M.canonicalMeasurementBoundary ≡ false
saraNotPlantDelivery = refl

foliarIsotopeNotNitrogenaseFlux :
  M.foliarIsotopeEstimateEqualsDirectNitrogenaseFlux M.canonicalMeasurementBoundary ≡ false
foliarIsotopeNotNitrogenaseFlux = refl

soilNNotBNFContribution :
  M.soilNPoolEqualsBNFContribution M.canonicalMeasurementBoundary ≡ false
soilNNotBNFContribution = refl

proxyDoesNotCloseBacterialFluxStage :
  M.activityProxyClosesGenericBacterialFixedNFlux M.canonicalMeasurementBoundary ≡ false
proxyDoesNotCloseBacterialFluxStage = refl
