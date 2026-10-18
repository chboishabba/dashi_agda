module DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Agriculture.AcaciaSenegalRhizobialBNFSourceAtlasExact as Acacia

fall2008DOIIsRecorded :
  Attribution.doiState (Acacia.attributedSource Acacia.fall2008) ≡
  Attribution.doiRecorded "10.1111/j.1472-765X.2008.02389.x"
fall2008DOIIsRecorded = refl

fall2008PMIDPinned : Acacia.pmid (Acacia.identifiers Acacia.fall2008) ≡ "18565139"
fall2008PMIDPinned = refl

fall2016DOIIsRecorded :
  Attribution.doiState (Acacia.attributedSource Acacia.fall2016) ≡
  Attribution.doiRecorded "10.3389/fpls.2016.01355"
fall2016DOIIsRecorded = refl

fall2016PMIDPinned : Acacia.pmid (Acacia.identifiers Acacia.fall2016) ≡ "27656192"
fall2016PMIDPinned = refl

fall2016PMCIDPinned : Acacia.pmcid (Acacia.identifiers Acacia.fall2016) ≡ "PMC5013129"
fall2016PMCIDPinned = refl

faye2006DOIIsRecorded :
  Attribution.doiState (Acacia.attributedSource Acacia.faye2006) ≡
  Attribution.doiRecorded "10.1080/15324980500369475"
faye2006DOIIsRecorded = refl

herrmann2012DOIIsRecorded :
  Attribution.doiState (Acacia.attributedSource Acacia.herrmann2012) ≡
  Attribution.doiRecorded "10.1016/j.agee.2011.12.014"
herrmann2012DOIIsRecorded = refl

hostSynonymDoesNotCollapseStudyIdentity :
  Acacia.hostSynonymImpliesSameStudy Acacia.canonicalAcaciaSourceBoundary ≡ false
hostSynonymDoesNotCollapseStudyIdentity = refl

rhizobialIdentityDoesNotCreateFixedNFlux :
  Acacia.rhizobialIdentityImpliesEffectiveFixedNFlux Acacia.canonicalAcaciaSourceBoundary ≡ false
rhizobialIdentityDoesNotCreateFixedNFlux = refl

inoculationDoesNotCreateNitrogenaseMediation :
  Acacia.inoculationResponseImpliesNitrogenaseMediation Acacia.canonicalAcaciaSourceBoundary ≡ false
inoculationDoesNotCreateNitrogenaseMediation = refl

gumYieldIsNotDirectFixationRate :
  Acacia.gumYieldResponseIsDirectFixationRate Acacia.canonicalAcaciaSourceBoundary ≡ false
gumYieldIsNotDirectFixationRate = refl

localSourceDoesNotCreateDeploymentAuthority :
  Acacia.localFieldResultImpliesDeploymentAuthority Acacia.canonicalAcaciaSourceBoundary ≡ false
localSourceDoesNotCreateDeploymentAuthority = refl
