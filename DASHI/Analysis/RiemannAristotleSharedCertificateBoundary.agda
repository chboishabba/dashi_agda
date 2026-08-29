module DASHI.Analysis.RiemannAristotleSharedCertificateBoundary where

open import DASHI.Core.Prelude

record SharedCertificateNonpromotionBoundary : Set where
  constructor shared-certificate-nonpromotion-boundary
  field
    sharedCertificateImpliesEndpointInequality : Bool
    sharedCertificateImpliesEndpointInequalityIsFalse :
      sharedCertificateImpliesEndpointInequality ≡ false
    exactReindexImpliesMultiZeroSeparation : Bool
    exactReindexImpliesMultiZeroSeparationIsFalse :
      exactReindexImpliesMultiZeroSeparation ≡ false
    architectureImpliesRH : Bool
    architectureImpliesRHIsFalse : architectureImpliesRH ≡ false

canonicalSharedCertificateNonpromotionBoundary : SharedCertificateNonpromotionBoundary
canonicalSharedCertificateNonpromotionBoundary =
  shared-certificate-nonpromotion-boundary false refl false refl false refl
