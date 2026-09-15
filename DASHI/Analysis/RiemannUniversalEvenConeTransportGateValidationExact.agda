module DASHI.Analysis.RiemannUniversalEvenConeTransportGateValidationExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannUniversalEvenConeTransportGateExact as P

transportBoundaryRegression :
  P.UniversalEvenConeTransportBoundary.sourceUniversalTaperOwned
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ true
  × P.UniversalEvenConeTransportBoundary.sameObjectTransportInterfaceSpecified
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ true
  × P.UniversalEvenConeTransportBoundary.nonnegativeTaperFeedsPositivePartMajorant
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ true
  × P.UniversalEvenConeTransportBoundary.sameObjectTransportPaid
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ false
transportBoundaryRegression = refl , refl , refl , refl

firewallRegression :
  P.UniversalEvenConeTransportBoundary.sourceExistenceCreatesAgdaTransport
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ false
  × P.UniversalEvenConeTransportBoundary.oeisNumericalPatternCreatesTaperTransport
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ false
  × P.UniversalEvenConeTransportBoundary.positivePartMajorantClosesGamma
    P.canonicalUniversalEvenConeTransportBoundary
  ≡ false
firewallRegression = refl , refl , refl
