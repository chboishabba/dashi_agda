module DASHI.Biology.Agriculture.AustralianTopsoilPropaguleBiotaCarrierRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianTopsoilPropaguleBiotaCarrierExact as T

golos2016Pinned : T.golosEtAl2016DOI ≡ "10.1111/rec.12389"
golos2016Pinned = refl

valliere2022Pinned : T.valliereEtAl2022DOI ≡ "10.1007/s11104-021-05217-z"
valliere2022Pinned = refl

stockpileAgeNotSeedFunction :
  T.stockpileAgeAloneDeterminesPropaguleRecruitment T.canonicalTopsoilCarrierBoundary ≡ false
stockpileAgeNotSeedFunction = refl

seedBankNotSymbiosis :
  T.seedBankConditionDeterminesRhizobialNodulationCapacity T.canonicalTopsoilCarrierBoundary ≡ false
seedBankNotSymbiosis = refl

physicochemistryNotBiologicalIntegrity :
  T.similarMeasuredPhysicochemistryImpliesSimilarBiologicalIntegrity T.canonicalTopsoilCarrierBoundary ≡ false
physicochemistryNotBiologicalIntegrity = refl

handlingContextRetained :
  T.stockpileDepthAgeHandlingAndOriginMustRemainIndexed T.canonicalTopsoilCarrierBoundary ≡ true
handlingContextRetained = refl

consumerRetained :
  T.restorationConsumerMustRemainIndexed T.canonicalTopsoilCarrierBoundary ≡ true
consumerRetained = refl

directTransferNotUniversalAuthority :
  T.directTransferBenefitCreatesUniversalTopsoilPrescription T.canonicalTopsoilCarrierBoundary ≡ false
directTransferNotUniversalAuthority = refl
