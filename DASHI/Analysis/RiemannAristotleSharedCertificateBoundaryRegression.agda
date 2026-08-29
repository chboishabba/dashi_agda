module DASHI.Analysis.RiemannAristotleSharedCertificateBoundaryRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleSharedCertificateBoundary as B

endpointNotManufactured :
  B.SharedCertificateNonpromotionBoundary.sharedCertificateImpliesEndpointInequality
    B.canonicalSharedCertificateNonpromotionBoundary ≡ false
endpointNotManufactured = refl

multiZeroNotManufactured :
  B.SharedCertificateNonpromotionBoundary.exactReindexImpliesMultiZeroSeparation
    B.canonicalSharedCertificateNonpromotionBoundary ≡ false
multiZeroNotManufactured = refl

rhNotManufactured :
  B.SharedCertificateNonpromotionBoundary.architectureImpliesRH
    B.canonicalSharedCertificateNonpromotionBoundary ≡ false
rhNotManufactured = refl
