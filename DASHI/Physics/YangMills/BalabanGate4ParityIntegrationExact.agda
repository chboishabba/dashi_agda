module DASHI.Physics.YangMills.BalabanGate4ParityIntegrationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R-Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- PURPOSE
-- Collect the exact invariance hypotheses under which parity improves powers
-- in Gate 4.  No odd contribution is cancelled without an identified physical
-- involution, measure invariance and the relevant covariance law.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
import DASHI.Physics.YangMills.BalabanFederbushPairedContourCancellationExact as Federbush
import DASHI.Physics.YangMills.BalabanP10P33PhysicalCutsetExact as P10P33
open import DASHI.Physics.YangMills.CompactLieProofLevel

record ContourParityLane : Set₁ where
  field
    Contour LogVector Scalar : Set
    logVector : Parity.ParityCodomain LogVector

    inverseContour : Parity.Involution Contour

    contourFamilyClosedUnderInverse : Set
    contourFamilyClosedUnderInverseEvidence :
      contourFamilyClosedUnderInverse

    inverseContourUsesLinkAndOrderReversal : Set
    inverseContourUsesLinkAndOrderReversalEvidence :
      inverseContourUsesLinkAndOrderReversal

    holonomyInverseUnderInverseContour : Set
    holonomyInverseUnderInverseContourEvidence :
      holonomyInverseUnderInverseContour

    pairedContourWeightsEqual : Set
    pairedContourWeightsEqualEvidence : pairedContourWeightsEqual

    commonPrincipalLogBranchForPairs : Set
    commonPrincipalLogBranchForPairsEvidence :
      commonPrincipalLogBranchForPairs

    pairedFirstJetCancellation : Set
    pairedFirstJetCancellationEvidence :
      pairedFirstJetCancellation

    pairedOddBCHTermsCancel : Set
    pairedOddBCHTermsCancelEvidence : pairedOddBCHTermsCancel

    quadraticCentreForcing : Set
    quadraticCentreForcingEvidence : quadraticCentreForcing

open ContourParityLane public

record BackgroundGaugeParityLane : Set₁ where
  field
    Background GaugeSource Constraint : Set

    backgroundInvolution : Parity.Involution Background
    sourceInvolution : Parity.Involution GaugeSource

    backgroundGaugeInvolutionCovariant : Set
    backgroundGaugeInvolutionCovariantEvidence :
      backgroundGaugeInvolutionCovariant

    sourceOddUnderGaugeInvolution : Set
    sourceOddUnderGaugeInvolutionEvidence :
      sourceOddUnderGaugeInvolution

    mixedNormInvariantUnderInvolution : Set
    mixedNormInvariantUnderInvolutionEvidence :
      mixedNormInvariantUnderInvolution

    backgroundConstraintEven : Set
    backgroundConstraintEvenEvidence : backgroundConstraintEven

open BackgroundGaugeParityLane public

record WilsonHessianParityLane : Set₁ where
  field
    Configuration Tangent ActionValue : Set

    configurationInvolution : Parity.Involution Configuration

    wilsonActionInvariantUnderOrientedInversion : Set
    wilsonActionInvariantUnderOrientedInversionEvidence :
      wilsonActionInvariantUnderOrientedInversion

    wilsonFirstDerivativeOdd : Set
    wilsonFirstDerivativeOddEvidence : wilsonFirstDerivativeOdd

    wilsonSecondDerivativeEven : Set
    wilsonSecondDerivativeEvenEvidence : wilsonSecondDerivativeEven

    wilsonThirdDerivativeOdd : Set
    wilsonThirdDerivativeOddEvidence : wilsonThirdDerivativeOdd

    pairedThirdDerivativeIntegralVanishes : Set
    pairedThirdDerivativeIntegralVanishesEvidence :
      pairedThirdDerivativeIntegralVanishes

open WilsonHessianParityLane public

record GaussianParityLane : Set₁ where
  field
    Fluctuation Integrand IntegralValue : Set

    fluctuationInvolution : Parity.Involution Fluctuation

    fluctuationMeasureSymmetric : Set
    fluctuationMeasureSymmetricEvidence :
      fluctuationMeasureSymmetric

    oddIntegrandIntegralZero : Set
    oddIntegrandIntegralZeroEvidence : oddIntegrandIntegralZero

    centeredGaussianOddMomentsZero : Set
    centeredGaussianOddMomentsZeroEvidence :
      centeredGaussianOddMomentsZero

    evenRemainderIntegratedBound : Set
    evenRemainderIntegratedBoundEvidence :
      evenRemainderIntegratedBound

open GaussianParityLane public

record ActivityParityLane : Set₁ where
  field
    Field Activity : Set

    fieldInvolution : Parity.Involution Field

    activityParityClassification : Set
    activityParityClassificationEvidence :
      activityParityClassification

    smallFieldActivityEven : Set
    smallFieldActivityEvenEvidence : smallFieldActivityEven

    boundaryActivityOrientationParity : Set
    boundaryActivityOrientationParityEvidence :
      boundaryActivityOrientationParity

    rOperationPreservesParityClass : Set
    rOperationPreservesParityClassEvidence :
      rOperationPreservesParityClass

    oddTaylorCoefficientsVanishForEvenActivity : Set
    oddTaylorCoefficientsVanishForEvenActivityEvidence :
      oddTaylorCoefficientsVanishForEvenActivity

    constantCoefficientVanishesForOddActivity : Set
    constantCoefficientVanishesForOddActivityEvidence :
      constantCoefficientVanishesForOddActivity

open ActivityParityLane public

record Gate4ParityPackage : Set₁ where
  field
    contour : ContourParityLane
    backgroundGauge : BackgroundGaugeParityLane
    wilsonHessian : WilsonHessianParityLane
    gaussian : GaussianParityLane
    activity : ActivityParityLane

    p10P33 : P10P33.P10P33PhysicalReceipt

    parityImprovesOnlyCertifiedChannels : Set
    parityImprovesOnlyCertifiedChannelsEvidence :
      parityImprovesOnlyCertifiedChannels

    noPhysicalEstimateReplacedByParityAlone : Set
    noPhysicalEstimateReplacedByParityAloneEvidence :
      noPhysicalEstimateReplacedByParityAlone

    theoremBoundary : String

open Gate4ParityPackage public

gate4ParityInterfaceLevel : ProofLevel
gate4ParityInterfaceLevel = machineChecked

contourWeightedInversionInputsLevel : ProofLevel
contourWeightedInversionInputsLevel = conditional

wilsonAndGaussianParityInputsLevel : ProofLevel
wilsonAndGaussianParityInputsLevel = conditional

activityParityPreservationInputsLevel : ProofLevel
activityParityPreservationInputsLevel = conditional
