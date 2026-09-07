module DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueProjectionNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source

------------------------------------------------------------------------
-- Carbon stewardship-value projection boundary.
--
-- The BIA source proposition is an agency policy classification: carbon is not
-- considered a trust asset under the cited forest/agricultural-product frame.
-- This file does NOT turn that agency category into a theorem about total
-- ecological, cultural, market or community value.
------------------------------------------------------------------------

data TrustAssetProjection : Set where
  notTrustAsset : TrustAssetProjection
  trustAsset : TrustAssetProjection


data StewardshipValueState : Set where
  storageValueLow : StewardshipValueState
  storageValueHigh : StewardshipValueState


data CarbonStewardshipState : Set where
  sameBiaCategoryLowUncapturedValue : CarbonStewardshipState
  sameBiaCategoryHighUncapturedValue : CarbonStewardshipState


trustAssetObserver : CarbonStewardshipState → TrustAssetProjection
trustAssetObserver sameBiaCategoryLowUncapturedValue = notTrustAsset
trustAssetObserver sameBiaCategoryHighUncapturedValue = notTrustAsset

stewardshipValueOutcome : CarbonStewardshipState → StewardshipValueState
stewardshipValueOutcome sameBiaCategoryLowUncapturedValue = storageValueLow
stewardshipValueOutcome sameBiaCategoryHighUncapturedValue = storageValueHigh

stewardshipValueDiffers :
  stewardshipValueOutcome sameBiaCategoryLowUncapturedValue ≡
  stewardshipValueOutcome sameBiaCategoryHighUncapturedValue → ⊥
stewardshipValueDiffers ()

canonicalTrustAssetNonFactorability :
  INF.NonFactorabilityWitness trustAssetObserver stewardshipValueOutcome
canonicalTrustAssetNonFactorability =
  INF.nonFactorabilityWitness
    sameBiaCategoryLowUncapturedValue
    sameBiaCategoryHighUncapturedValue
    refl
    stewardshipValueDiffers

trustAssetCategoryCannotFactorStewardshipValue :
  INF.FactorsThrough trustAssetObserver stewardshipValueOutcome → ⊥
trustAssetCategoryCannotFactorStewardshipValue =
  INF.witnessRulesOutEveryFlatFactorisation canonicalTrustAssetNonFactorability

anyTrustAssetReclassificationStillCannotRecoverValue :
  ∀ {Recharted : Set} →
  (rechart : TrustAssetProjection → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (trustAssetObserver state))
    stewardshipValueOutcome → ⊥
anyTrustAssetReclassificationStillCannotRecoverValue rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart canonicalTrustAssetNonFactorability

------------------------------------------------------------------------
-- Source authority remains explicit.
------------------------------------------------------------------------

biaSourceIsAdministrativePolicy :
  Source.authorityKind Source.biaCarbon2023Authority ≡ Source.officialAdministrativePolicy
biaSourceIsAdministrativePolicy = refl

biaSourceIsGovernmentAuthored :
  Source.analysisAuthorIsGovernment Source.biaCarbon2023Authority ≡ true
biaSourceIsGovernmentAuthored = refl

biaSourceDoesNotPermitUniversalGeneralisation :
  Source.universalGeneralisationAllowed Source.biaCarbon2023Authority ≡ false
biaSourceDoesNotPermitUniversalGeneralisation = refl

------------------------------------------------------------------------
-- Distinct carbon-value coordinates.
------------------------------------------------------------------------

data CarbonValueCoordinate : Set where
  agencyTrustAssetClassification : CarbonValueCoordinate
  voluntaryMarketCreditPrice : CarbonValueCoordinate
  socialCarbonMitigationValuation : CarbonValueCoordinate
  ecosystemServiceValuation : CarbonValueCoordinate
  indigenousStewardshipValue : CarbonValueCoordinate
  culturalRelationalValue : CarbonValueCoordinate


record CarbonValueCoordinateBoundary : Set where
  constructor carbonValueCoordinateBoundary
  field
    legalCategory : CarbonValueCoordinate
    marketCategory : CarbonValueCoordinate
    socialValuationCategory : CarbonValueCoordinate
    communityValueCategory : CarbonValueCoordinate
    sameCoordinateClaimed : Bool
    sameCoordinateClaimedIsFalse : sameCoordinateClaimed ≡ false
open CarbonValueCoordinateBoundary public

canonicalCarbonValueCoordinates : CarbonValueCoordinateBoundary
canonicalCarbonValueCoordinates = carbonValueCoordinateBoundary
  agencyTrustAssetClassification
  voluntaryMarketCreditPrice
  socialCarbonMitigationValuation
  indigenousStewardshipValue
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data TrustAssetClassificationEqualsStewardshipValue : Set where
data CarbonMarketPriceEqualsSocialCarbonValue : Set where
data AgencyNonAssetClassificationMeansNoEconomicValue : Set where
data StoredCarbonValueRequiresExtractionFrame : Set where

trustCategoryDoesNotEqualStewardshipValue : TrustAssetClassificationEqualsStewardshipValue → ⊥
trustCategoryDoesNotEqualStewardshipValue ()
marketPriceDoesNotEqualSocialValue : CarbonMarketPriceEqualsSocialCarbonValue → ⊥
marketPriceDoesNotEqualSocialValue ()
nonAssetClassificationDoesNotMeanNoValue : AgencyNonAssetClassificationMeansNoEconomicValue → ⊥
nonAssetClassificationDoesNotMeanNoEconomicValue ()
storageValueDoesNotRequireExtractionFrame : StoredCarbonValueRequiresExtractionFrame → ⊥
storageValueDoesNotRequireExtractionFrame ()
