module DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierExact as P

vendoredBishopIsOwned :
  P.vendoredBishopBackendOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
vendoredBishopIsOwned = refl

finiteSumBridgeIsOwned :
  P.finiteSumToBishopSeriesBridgeOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
finiteSumBridgeIsOwned = refl

absoluteToLimitCompilerIsOwned :
  P.absoluteConvergenceToLimitCompilerOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
absoluteToLimitCompilerIsOwned = refl

bishopComplexLiftIsOwned :
  P.bishopComplexComponentwiseConvergenceOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopComplexLiftIsOwned = refl

sameCarrierConcreteComplexLimitCompilerIsOwned :
  P.sameCarrierConcreteComplexLimitCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
sameCarrierConcreteComplexLimitCompilerIsOwned = refl

coefficientPolynomialGrowthIsOwned :
  P.eisensteinCoefficientPolynomialGrowthOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
coefficientPolynomialGrowthIsOwned = refl

literalTruncationIncrementIdentityIsOwned :
  P.literalTruncationIncrementIdentityOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
literalTruncationIncrementIdentityIsOwned = refl

literalIncrementCoefficientEnvelopeIsOwned :
  P.literalIncrementCoefficientEnvelopeOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
literalIncrementCoefficientEnvelopeIsOwned = refl

principalStripQModulusCompilerIsOwned :
  P.principalStripQModulusCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
principalStripQModulusCompilerIsOwned = refl

upperHalfPlaneQDecayCompilerIsOwned :
  P.upperHalfPlaneQDecayCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
upperHalfPlaneQDecayCompilerIsOwned = refl

concreteQOrderAndStripInputsStillUnpaid :
  P.concreteQOrderAndStripInputsOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
concreteQOrderAndStripInputsStillUnpaid = refl

constructedEvaluatorCarrierWeldIsStillUnpaid :
  P.constructedComplexEvaluatorCarrierWeldOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ false
constructedEvaluatorCarrierWeldIsStillUnpaid = refl

e4MajorantIsStillUnpaid :
  P.e4ConcreteAbsoluteConvergenceOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ false
e4MajorantIsStillUnpaid = refl

e6MajorantIsStillUnpaid :
  P.e6ConcreteAbsoluteConvergenceOwned P.canonicalEisensteinBishopConvergenceFrontier ≡ false
e6MajorantIsStillUnpaid = refl

analyticSameObjectIsStillUnpaid :
  P.bishopLimitEqualsAnalyticLatticeEisenstein P.canonicalEisensteinBishopConvergenceFrontier ≡ false
analyticSameObjectIsStillUnpaid = refl
