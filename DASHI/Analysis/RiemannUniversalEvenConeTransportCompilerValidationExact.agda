module DASHI.Analysis.RiemannUniversalEvenConeTransportCompilerValidationExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannUniversalEvenConeTransportGateExact as T

compilerRegression :
  T.UniversalEvenConeTransportBoundary.gammaRepresentationAttachmentCompilerAvailable
    T.canonicalUniversalEvenConeTransportBoundary
  ≡ true
  × T.UniversalEvenConeTransportBoundary.offRepresentationAttachmentUsesTransportedTaper
    T.canonicalUniversalEvenConeTransportBoundary
  ≡ true
  × T.UniversalEvenConeTransportBoundary.offRepresentationAttachmentStillNeedsCutoffReceipt
    T.canonicalUniversalEvenConeTransportBoundary
  ≡ true
compilerRegression = refl , refl , refl

paymentRegression :
  T.UniversalEvenConeTransportBoundary.sameObjectTransportPaid
    T.canonicalUniversalEvenConeTransportBoundary
  ≡ false
  × T.UniversalEvenConeTransportBoundary.positivePartMajorantAuthorityPaid
    T.canonicalUniversalEvenConeTransportBoundary
  ≡ false
paymentRegression = refl , refl
