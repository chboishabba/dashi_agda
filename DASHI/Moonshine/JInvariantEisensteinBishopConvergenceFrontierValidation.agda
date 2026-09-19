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

concreteMurrayBishopSetoidBackendIsOwned :
  P.concreteMurrayBishopSetoidBackendOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
concreteMurrayBishopSetoidBackendIsOwned = refl

bishopSetoidComplexAlgebraIsOwned :
  P.bishopSetoidComplexAlgebraOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopSetoidComplexAlgebraIsOwned = refl

bishopNatCoefficientEmbeddingBridgesAreOwned :
  P.bishopNatCoefficientEmbeddingBridgesOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopNatCoefficientEmbeddingBridgesAreOwned = refl

bishopSetoidEisensteinSeriesFromPowerEnvelopeIsOwned :
  P.bishopSetoidEisensteinSeriesFromPowerEnvelopeOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopSetoidEisensteinSeriesFromPowerEnvelopeIsOwned = refl

bishopQPowerComponentEnvelopeStillUnpaid :
  P.bishopQPowerComponentEnvelopeInhabited
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
bishopQPowerComponentEnvelopeStillUnpaid = refl

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

qPowerModulusPropagationCompilerIsOwned :
  P.qPowerModulusPropagationCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
qPowerModulusPropagationCompilerIsOwned = refl

polynomialGeometricIncrementModulusCompilerIsOwned :
  P.polynomialGeometricIncrementModulusCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
polynomialGeometricIncrementModulusCompilerIsOwned = refl

genericDominatedTailCompilerIsOwned :
  P.genericDominatedTailCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
genericDominatedTailCompilerIsOwned = refl

bishopPolynomialGeometricComparisonCompilerIsOwned :
  P.bishopPolynomialGeometricComparisonCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopPolynomialGeometricComparisonCompilerIsOwned = refl

bishopStrictRatioInterpolationIsOwned :
  P.bishopStrictRatioInterpolationOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopStrictRatioInterpolationIsOwned = refl

bishopPolynomialSuccessorFactorLimitIsOwned :
  P.bishopPolynomialSuccessorFactorLimitOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopPolynomialSuccessorFactorLimitIsOwned = refl

bishopFixedDegreePolynomialGeometricConvergenceIsOwned :
  P.bishopFixedDegreePolynomialGeometricConvergenceOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopFixedDegreePolynomialGeometricConvergenceIsOwned = refl

bishopFixedDegreePolynomialGeometricAbsoluteConvergenceIsOwned :
  P.bishopFixedDegreePolynomialGeometricAbsoluteConvergenceOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopFixedDegreePolynomialGeometricAbsoluteConvergenceIsOwned = refl

bishopShiftedScaledPolynomialGeometricAbsoluteConvergenceIsOwned :
  P.bishopShiftedScaledPolynomialGeometricAbsoluteConvergenceOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopShiftedScaledPolynomialGeometricAbsoluteConvergenceIsOwned = refl

bishopEisensteinMajorantSpecializationIsOwned :
  P.bishopEisensteinMajorantSpecializationOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopEisensteinMajorantSpecializationIsOwned = refl

bishopLiteralRadiusWeldCompilerIsOwned :
  P.bishopLiteralRadiusWeldCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopLiteralRadiusWeldCompilerIsOwned = refl

bishopFiniteCauchyWingIsOwned :
  P.bishopFiniteCauchyWingOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopFiniteCauchyWingIsOwned = refl

bishopExponentialAdditivityIsOwned :
  P.bishopExponentialAdditivityOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopExponentialAdditivityIsOwned = refl

bishopGlobalNegativeExponentialUnitIntervalIsOwned :
  P.bishopGlobalNegativeExponentialUnitIntervalOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopGlobalNegativeExponentialUnitIntervalIsOwned = refl

bishopUpperHalfPlaneRadiusIsOwned :
  P.bishopUpperHalfPlaneRadiusOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopUpperHalfPlaneRadiusIsOwned = refl

bishopUpperHalfPlaneEisensteinMajorantsAreOwned :
  P.bishopUpperHalfPlaneEisensteinMajorantsOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopUpperHalfPlaneEisensteinMajorantsAreOwned = refl

bishopUpperHalfPlaneQuotientRadiusWeldCompilerIsOwned :
  P.bishopUpperHalfPlaneQuotientRadiusWeldCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopUpperHalfPlaneQuotientRadiusWeldCompilerIsOwned = refl

literalQToBishopRadiusReductionCompilerIsOwned :
  P.literalQToBishopRadiusReductionCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
literalQToBishopRadiusReductionCompilerIsOwned = refl

qExponentMagnitudeToLiteralExponentCompilerIsOwned :
  P.qExponentMagnitudeToLiteralExponentCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
qExponentMagnitudeToLiteralExponentCompilerIsOwned = refl

qMagnitudeCoordinateTransportCompilerIsOwned :
  P.qMagnitudeCoordinateTransportCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
qMagnitudeCoordinateTransportCompilerIsOwned = refl

bishopLiteralRadiusMajorantCompilerIsOwned :
  P.bishopLiteralRadiusMajorantCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopLiteralRadiusMajorantCompilerIsOwned = refl

canonicalBishopQuotientRadiusRelationIsOwned :
  P.canonicalBishopQuotientRadiusRelationOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
canonicalBishopQuotientRadiusRelationIsOwned = refl

literalQToBishopRadiusSameObjectStillUnpaid :
  P.literalQToBishopRadiusSameObjectOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
literalQToBishopRadiusSameObjectStillUnpaid = refl

bishopDegreeFourPolynomialGeometricConvergenceIsOwned :
  P.bishopDegreeFourPolynomialGeometricConvergenceOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopDegreeFourPolynomialGeometricConvergenceIsOwned = refl

bishopDegreeSixPolynomialGeometricConvergenceIsOwned :
  P.bishopDegreeSixPolynomialGeometricConvergenceOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
bishopDegreeSixPolynomialGeometricConvergenceIsOwned = refl

genericTailToCauchyBridgeIsOwned :
  P.genericTailToCauchyBridgeOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
genericTailToCauchyBridgeIsOwned = refl

selectedTailToCauchyBridgeStillUnpaid :
  P.selectedTailToCauchyBridgeInhabited
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
selectedTailToCauchyBridgeStillUnpaid = refl

fastCauchyLegacyQuotientInterfaceWeldIsOwned :
  P.fastCauchyLegacyQuotientInterfaceWeldOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
fastCauchyLegacyQuotientInterfaceWeldIsOwned = refl

genericSetoidComplexQuotientRingWeldIsOwned :
  P.genericSetoidComplexQuotientRingWeldOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
genericSetoidComplexQuotientRingWeldIsOwned = refl

fastCauchySetQuotientComplexCompatibilityCompilerIsOwned :
  P.fastCauchySetQuotientComplexCompatibilityCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
fastCauchySetQuotientComplexCompatibilityCompilerIsOwned = refl

concreteLegacyQuotientStillUnpaid :
  P.concreteLegacyQuotientInhabited
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
concreteLegacyQuotientStillUnpaid = refl

sameCarrierModulusAlgebraStillUnpaid :
  P.sameCarrierModulusAlgebraInhabited
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
sameCarrierModulusAlgebraStillUnpaid = refl

modulusMultiplicationFactorCompilerIsOwned :
  P.modulusMultiplicationFactorCompilerOwned
    P.canonicalEisensteinBishopConvergenceFrontier ≡ true
modulusMultiplicationFactorCompilerIsOwned = refl

complexNormSquareCompositionStillUnpaid :
  P.complexNormSquareCompositionInhabited
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
complexNormSquareCompositionStillUnpaid = refl

nonnegativeSquareRootMultiplicationStillUnpaid :
  P.nonnegativeSquareRootMultiplicationInhabited
    P.canonicalEisensteinBishopConvergenceFrontier ≡ false
nonnegativeSquareRootMultiplicationStillUnpaid = refl

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
