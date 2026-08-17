module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound57HyperoctahedralWalshValidation where

------------------------------------------------------------------------
-- ROUND 57 FOCUSED VALIDATION ROOT
--
-- Cross-pollination from the finite-character discipline of PR #572 is used
-- only structurally:
--
--   actual finite carrier -> action -> characters/orbits -> exact cancellation
--   -> interval arithmetic.
--
-- No C3/C9/F9 object is imported into Yang--Mills.
--
-- BETA / L3
--   generated 4^4 grid
--     -> exact B4 generator action
--     -> regular geometric counts 64+96+64+16
--     -> conservative fixed-axis counts 48+48+16+16+48+48+16
--     -> joint momentum action on actual DiagramExpression syntax
--     -> literal source equivariance reduced to 7 B4-generator equations
--        or 6 fixed-axis equations
--     -> every finite generator word fixes the expression
--     -> atom-level generated-box environment covariance transports through
--        the SAME recursive expression evaluator
--     -> whole-expression RationalInterval equality across symmetry boxes
--     -> C2^4 Walsh--Fourier sign projection
--     -> exact nontrivial sign-sector orbit cancellation
--     -> four- or seven-representative finite sum arithmetic.
--
-- G2
--   same Subset4 carrier keeps TWO structures separate:
--     Boolean incidence/Mobius localisation;
--     C2^4 symmetric-difference/Walsh--Fourier characters.
--   Without assuming XOR convolution, the safer simultaneous-S4 signature
--   reduction gives 4 raw degree representatives and at most 26 ordered Green
--   pair representatives instead of 15 and 225.
--
-- Physical source equivariance remains a literal theorem obligation.  The
-- existing source-facing regularIntegrand is still abstract DiagramExpression
-- data, so this root does not manufacture an invariance proof for it.  The new
-- generator certificate makes that obligation finite and source-auditable;
-- the evaluation-transport theorem removes any need for 240 independent
-- whole-expression interval receipts once atom covariance is instantiated.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound56PiBetaG2Validation as R56
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as GridOrbit
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopSignCharacterProjectionExact as SignProjection
import DASHI.Physics.YangMills.BalabanClayT4SignOrbitGlobalCancellationExact as SignOrbit
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact as Joint
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopHyperoctahedralGeneratorCertificateExact as GeneratorCertificate
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact as EvaluationTransport
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact as OrbitSum
import DASHI.Physics.YangMills.BalabanP33SelectedGreenSubsetOrbitReductionExact as G2Orbit

hyperoctahedralGridGeneratorActionLevel =
  GridOrbit.hyperoctahedralGridGeneratorActionLevel
regularFourOrbitClassificationLevel =
  GridOrbit.regularFourOrbitClassificationLevel
fixedAxisSevenOrbitClassificationLevel =
  GridOrbit.fixedAxisSevenOrbitClassificationLevel

booleanFourCubeWalshCharacterLevel =
  Walsh.booleanFourCubeWalshCharacterLevel
nontrivialWalshOrbitCancellationLevel =
  Walsh.nontrivialWalshOrbitCancellationLevel
mobiusWalshSeparationLevel = Walsh.mobiusWalshSeparationLevel

signCharacterProjectionLevel = SignProjection.signCharacterProjectionLevel
nontrivialSignCharacterProjectionCancellationLevel =
  SignProjection.nontrivialSignCharacterProjectionCancellationLevel
nontrivialCharacterGlobalOrbitCancellationLevel =
  SignOrbit.nontrivialCharacterGlobalOrbitCancellationLevel

jointMomentumSyntaxActionLevel = Joint.jointMomentumSyntaxActionLevel
literalTrigParityUnderJointActionLevel = Joint.literalTrigParityUnderJointActionLevel
literalHatMomentumScalarActionLevel = Joint.literalHatMomentumScalarActionLevel
literalRegularIntegrandJointEquivarianceLevel =
  Joint.literalRegularIntegrandJointEquivarianceLevel

sevenGeneratorReductionLevel =
  GeneratorCertificate.sevenGeneratorReductionLevel
finiteGeneratorWordClosureLevel =
  GeneratorCertificate.finiteGeneratorWordClosureLevel
sixGeneratorFixedAxisReductionLevel =
  GeneratorCertificate.sixGeneratorFixedAxisReductionLevel
literalRegularIntegrandFiniteGeneratorCertificateLevel =
  GeneratorCertificate.literalRegularIntegrandFiniteGeneratorCertificateLevel

generatorEvaluationTransportLevel =
  EvaluationTransport.generatorEvaluationTransportLevel
literalRegularIntegrandIntervalTransportLevel =
  EvaluationTransport.literalRegularIntegrandIntervalTransportLevel
literalGeneratedBoxAtomCovarianceLevel =
  EvaluationTransport.literalGeneratedBoxAtomCovarianceLevel

fourOrbitFiniteSumReductionLevel = OrbitSum.fourOrbitFiniteSumReductionLevel
sevenOrbitFiniteSumReductionLevel = OrbitSum.sevenOrbitFiniteSumReductionLevel
literalFourOrbitBoxCertificateLevel = OrbitSum.literalFourOrbitBoxCertificateLevel
literalFixedAxisSevenOrbitBoxCertificateLevel =
  OrbitSum.literalFixedAxisSevenOrbitBoxCertificateLevel

rawFourDegreeReductionLevel = G2Orbit.rawFourDegreeReductionLevel
greenTwentySixPairOrbitFiniteArithmeticLevel =
  G2Orbit.greenTwentySixPairOrbitFiniteArithmeticLevel
selectedRawSubsetS4EquivarianceLevel =
  G2Orbit.selectedRawSubsetS4EquivarianceLevel
selectedGreenSubsetS4EquivarianceLevel =
  G2Orbit.selectedGreenSubsetS4EquivarianceLevel
