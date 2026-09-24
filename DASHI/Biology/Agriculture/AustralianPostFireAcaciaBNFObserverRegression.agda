module DASHI.Biology.Agriculture.AustralianPostFireAcaciaBNFObserverRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianPostFireAcaciaBNFObserverExact as O

hamilton1993DOIPinned :
  O.hamiltonEtAl1993DOI ≡ "10.1016/0378-1127(93)90119-8"
hamilton1993DOIPinned = refl

guinto2000DOIPinned :
  O.guintoEtAl2000DOI ≡ "10.1139/x99-183"
guinto2000DOIPinned = refl

methodNameNotAdequacy :
  O.naturalAbundanceMethodNameImpliesAdequateEstimator O.canonicalPostFireObserverBoundary ≡ false
methodNameNotAdequacy = refl

baselineRetained :
  O.baselineHomogeneityMayBeDropped O.canonicalPostFireObserverBoundary ≡ false
baselineRetained = refl

referenceRetained :
  O.referencePlantIdentityMayBeDropped O.canonicalPostFireObserverBoundary ≡ false
referenceRetained = refl

fireSiteRetained :
  O.fireFrequencyAndSiteMayBeDropped O.canonicalPostFireObserverBoundary ≡ false
fireSiteRetained = refl

nDfaNotFlux :
  O.percentNdfaImpliesDirectFixedNFlux O.canonicalPostFireObserverBoundary ≡ false
nDfaNotFlux = refl

methodAgreementNotUniversal :
  O.methodAgreementAtOneSiteImpliesUniversalMethodAgreement O.canonicalPostFireObserverBoundary ≡ false
methodAgreementNotUniversal = refl

referenceSensitivityNotNoise :
  O.referencePlantSensitivityMayBeDiscardedAsNoise O.canonicalPostFireObserverBoundary ≡ false
referenceSensitivityNotNoise = refl
