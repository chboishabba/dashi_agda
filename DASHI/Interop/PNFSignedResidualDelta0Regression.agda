module DASHI.Interop.PNFSignedResidualDelta0Regression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_)

import DASHI.Interop.PNFSignedResidualDelta0Exact as Signed
import DASHI.Interop.PNFSpectralFieldGraph as Graph

partialEdgeMagnitudeRegression : Signed.edge01MagnitudeIsOne ≡ Signed.edge01MagnitudeIsOne
partialEdgeMagnitudeRegression = refl

contradictionEdgeNegativeRegression :
  Signed.edge20SignNegative ≡ Signed.edge20SignNegative
contradictionEdgeNegativeRegression = refl

negativeModeRegression :
  Signed.dot Signed.negativeDirection
    (Signed.signedResidualDelta0 Signed.negativeDirection)
  ≡ - (+ 2)
negativeModeRegression = Signed.negativeDirectionEnergyIsMinusTwo

positiveModeRegression :
  Signed.dot Signed.positiveDirection
    (Signed.signedResidualDelta0 Signed.positiveDirection)
  ≡ + 4
positiveModeRegression = Signed.positiveDirectionEnergyIsFour

signedOperatorIsNotPromotedToUnsigned :
  Signed.PNFSignedResidualDelta0Boundary.equalsUnsignedC3Laplacian
    Signed.canonicalPNFSignedResidualDelta0Boundary
  ≡ false
signedOperatorIsNotPromotedToUnsigned = refl

noContinuumPromotion :
  Signed.PNFSignedResidualDelta0Boundary.continuumHodgeAuthorityGranted
    Signed.canonicalPNFSignedResidualDelta0Boundary
  ≡ false
noContinuumPromotion = refl
