module DASHI.Interop.SLRProviderNormalisationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRProviderNormalisationExact as Norm
import DASHI.Interop.SLRSprint2CanonicalEvidenceConvergenceExact as Sprint2

m23RemainsPaid : Sprint2.m23State ≡ Sprint2.paid
m23RemainsPaid = refl

m24AwaitsRuntimeReceipt :
  Sprint2.m24State ≡ Sprint2.implementedAwaitingRuntime
m24AwaitsRuntimeReceipt = refl

wikidataUsesSharedCanonicalCarrier :
  Norm.wikidataUsesCanonicalCarrier Norm.canonicalProviderNormalisationParity ≡ true
wikidataUsesSharedCanonicalCarrier = refl

wikipediaUsesSharedCanonicalCarrier :
  Norm.wikipediaUsesCanonicalCarrier Norm.canonicalProviderNormalisationParity ≡ true
wikipediaUsesSharedCanonicalCarrier = refl

oalcUsesSharedCanonicalCarrier :
  Norm.oalcUsesCanonicalCarrier Norm.canonicalProviderNormalisationParity ≡ true
oalcUsesSharedCanonicalCarrier = refl

cachedLegalUsesSharedCanonicalCarrier :
  Norm.cachedLegalUsesCanonicalCarrier Norm.canonicalProviderNormalisationParity ≡ true
cachedLegalUsesSharedCanonicalCarrier = refl

providerCannotBypassReview :
  Norm.ProviderSpecificReviewBypassesCanonicalReview → ⊥
providerCannotBypassReview =
  Norm.providerSpecificReviewCannotBypassCanonicalReview

providerCannotBypassSharedReducer :
  Norm.ProviderSpecificProjectionBypassesSharedReducer → ⊥
providerCannotBypassSharedReducer =
  Norm.providerSpecificProjectionCannotBypassSharedReducer

cacheHitCannotRequireNetwork :
  Norm.ExactPgHitRequiresNetwork → ⊥
cacheHitCannotRequireNetwork =
  Norm.exactPgHitDoesNotRequireNetwork


cacheFirstPathIsRetained :
  Norm.cacheFirstPathRetainedInNormalisationReceipt
    Norm.canonicalProviderNormalisationParity
  ≡ true
cacheFirstPathIsRetained = refl

cacheFirstAcquisitionCountIsRetained :
  Norm.acquisitionNetworkCountRetained
    Norm.canonicalProviderNormalisationParity
  ≡ true
cacheFirstAcquisitionCountIsRetained = refl

cacheFirstVerificationCountIsRetained :
  Norm.verificationNetworkCountRetained
    Norm.canonicalProviderNormalisationParity
  ≡ true
cacheFirstVerificationCountIsRetained = refl
