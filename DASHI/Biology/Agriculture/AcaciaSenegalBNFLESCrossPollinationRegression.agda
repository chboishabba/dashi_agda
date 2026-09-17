module DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalBNFLESCrossPollinationExact as Bridge

abakerDOIRetained : Bridge.abakerDrylandDOI ≡ "10.1016/j.jaridenv.2017.12.004"
abakerDOIRetained = refl

soilNNotTreeOnly :
  Bridge.treeIdentityAloneAdequateForSoilN Bridge.canonicalAcaciaBNFLESBoundary ≡ false
soilNNotTreeOnly = refl

soilNNotNoduleOnly :
  Bridge.nodulePresenceAloneAdequateForSoilN Bridge.canonicalAcaciaBNFLESBoundary ≡ false
soilNNotNoduleOnly = refl

fixedNNotRhizobiumIdentityOnly :
  Bridge.rhizobialIdentityAloneAdequateForFixedN Bridge.canonicalAcaciaBNFLESBoundary ≡ false
fixedNNotRhizobiumIdentityOnly = refl

restorationNotFixedNOnly :
  Bridge.fixedNMetricAloneAdequateForRestoration Bridge.canonicalAcaciaBNFLESBoundary ≡ false
restorationNotFixedNOnly = refl

waterCarbonStudyNotRewrittenAsBNF :
  Bridge.abakerStudyMeasuredBNF Bridge.canonicalAcaciaBNFLESBoundary ≡ false
waterCarbonStudyNotRewrittenAsBNF = refl

fixedNDoesNotCreatePlantAssimilation :
  Bridge.fixedNFluxImpliesPlantAssimilation Bridge.canonicalAcaciaBNFLESBoundary ≡ false
fixedNDoesNotCreatePlantAssimilation = refl

soilNDoesNotCreateDeploymentAuthority :
  Bridge.soilNOutcomeImpliesDeploymentAuthority Bridge.canonicalAcaciaBNFLESBoundary ≡ false
soilNDoesNotCreateDeploymentAuthority = refl
