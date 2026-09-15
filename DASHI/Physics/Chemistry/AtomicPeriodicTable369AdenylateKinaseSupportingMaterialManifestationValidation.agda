module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSupportingMaterialManifestationValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSupportingMaterialManifestationExact as P

identityRegression :
  P.SupportingMaterialManifestationBoundary.adkArticleIdentityPaid
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ true
  × P.SupportingMaterialManifestationBoundary.legacyFootnotePiiObserved
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ true
  × P.SupportingMaterialManifestationBoundary.legacyFootnotePiiResolvesToDifferentArticle
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ true
identityRegression = refl , refl , refl

failClosedRegression :
  P.SupportingMaterialManifestationBoundary.legacyFootnoteMayPayAdkSupplement
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ false
  × P.SupportingMaterialManifestationBoundary.foreignSupplementMayPayCalibrationNumber
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ false
  × P.SupportingMaterialManifestationBoundary.unverifiedFigureReadoutMayPayNumericCell
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ false
failClosedRegression = refl , refl , refl

acquisitionRegression :
  P.SupportingMaterialManifestationBoundary.pmcAttachedSupportingMaterialRetained
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ true
  × P.SupportingMaterialManifestationBoundary.machineReadableSourcePreferred
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ true
  × P.SupportingMaterialManifestationBoundary.sameObjectManifestationRequiredBeforeNumericPromotion
    P.canonicalSupportingMaterialManifestationBoundary
  ≡ true
acquisitionRegression = refl , refl , refl
