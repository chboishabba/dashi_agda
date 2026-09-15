module DASHI.ComputerScience.RSA260BidiActionConsumerSufficiencyValidationExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.RSA260BidiActionConsumerSufficiencyExact as P

bidiRegression :
  P.RSAActionConsumerSufficiencyBoundary.consumerIndexedSufficiencyIsPrimary
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ true
  × P.RSAActionConsumerSufficiencyBoundary.collisionReopensResidualCoordinate
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ true
  × P.RSAActionConsumerSufficiencyBoundary.exactReplayRemainsSufficientUpperEndpoint
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ true
  × P.RSAActionConsumerSufficiencyBoundary.receiptIdentityMinimalityTransfersToAction
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ false
bidiRegression = refl , refl , refl , refl

paymentRegression :
  P.RSAActionConsumerSufficiencyBoundary.currentTwelveWorldDegreeR2R10AdequacyPaid
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ true
  × P.RSAActionConsumerSufficiencyBoundary.broaderThirtyFourWorldAdequacyPaid
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ false
  × P.RSAActionConsumerSufficiencyBoundary.productionCADOSameObjectAdequacyPaid
    P.canonicalRSAActionConsumerSufficiencyBoundary
  ≡ false
paymentRegression = refl , refl , refl
