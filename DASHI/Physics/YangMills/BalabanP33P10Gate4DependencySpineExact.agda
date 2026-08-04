module DASHI.Physics.YangMills.BalabanP33P10Gate4DependencySpineExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215753.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban. II. Large Fields",
-- Journal of Mathematical Physics 54 (2013), 092301.
-- DOI: 10.1063/1.4821275.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- PURPOSE
-- Encode the mathematically correct dependency order at the type level:
-- transverse Hessian coercivity and inverse control (P33) are constructed
-- before large-field suppression (P10), and both are consumed by seven
-- separate Gate-4 packages.  This prevents a monolithic Gate4 token from
-- silently supplying its own inverse, determinant, or activity estimates.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanP10P33PhysicalCutsetExact as Existing
import DASHI.Physics.YangMills.BalabanGate4ParityIntegrationExact as Parity
open import DASHI.Physics.YangMills.CompactLieProofLevel

record P33CoerciveInversePackage : Set₁ where
  field
    Configuration Tangent TransverseTangent Scalar : Set
    Hessian ReferenceHessian InverseHessian : Set

    wilsonActionSecondVariation : Set
    wilsonActionSecondVariationEvidence :
      wilsonActionSecondVariation

    constraintTangentCharacterisation : Set
    constraintTangentCharacterisationEvidence :
      constraintTangentCharacterisation

    gaugeNormalDecomposition : Set
    gaugeNormalDecompositionEvidence : gaugeNormalDecomposition

    referenceTransverseCoercivity : Set
    referenceTransverseCoercivityEvidence :
      referenceTransverseCoercivity

    backgroundHessianPerturbationBound : Set
    backgroundHessianPerturbationBoundEvidence :
      backgroundHessianPerturbationBound

    perturbationBelowReferenceFloor : Set
    perturbationBelowReferenceFloorEvidence :
      perturbationBelowReferenceFloor

    physicalTransverseCoercivity : Set
    physicalTransverseCoercivityEvidence :
      physicalTransverseCoercivity

    constrainedHessianInverseExists : Set
    constrainedHessianInverseExistsEvidence :
      constrainedHessianInverseExists

    uniformInverseNormBound : Set
    uniformInverseNormBoundEvidence : uniformInverseNormBound

    inverseKernelExponentialDecay : Set
    inverseKernelExponentialDecayEvidence :
      inverseKernelExponentialDecay

    legacyP33Chain : Existing.P33LinkEllipticityPhysicalChain
    theoremBoundary : String

open P33CoerciveInversePackage public

record P10SuppressionAfterP33
    (p33 : P33CoerciveInversePackage) : Set₁ where
  field
    LargeFieldSector Plaquette Defect Action Integral Activity : Set

    largeFieldWitnessPlaquette : Set
    largeFieldWitnessPlaquetteEvidence : largeFieldWitnessPlaquette

    wilsonActionPlaquetteLowerBound : Set
    wilsonActionPlaquetteLowerBoundEvidence :
      wilsonActionPlaquetteLowerBound

    largeFieldActionLowerBound : Set
    largeFieldActionLowerBoundEvidence : largeFieldActionLowerBound

    su2PrincipalChartValid : Set
    su2PrincipalChartValidEvidence : su2PrincipalChartValid

    haarJacobianBounds : Set
    haarJacobianBoundsEvidence : haarJacobianBounds

    wilsonTaylorRemainderBound : Set
    wilsonTaylorRemainderBoundEvidence :
      wilsonTaylorRemainderBound

    determinantCorrectionUsesP33Inverse : Set
    determinantCorrectionUsesP33InverseEvidence :
      determinantCorrectionUsesP33Inverse

    largeFieldIntegralSuppression : Set
    largeFieldIntegralSuppressionEvidence :
      largeFieldIntegralSuppression

    largeFieldActivityCompatibleWithKP : Set
    largeFieldActivityCompatibleWithKPEvidence :
      largeFieldActivityCompatibleWithKP

    legacyP10Chain : Existing.P10LargeFieldPhysicalChain
    theoremBoundary : String

open P10SuppressionAfterP33 public

record Gate4ExactContourPairing : Set₁ where
  field
    Contour : Set
    contourPartner : Contour → Contour

    contourPartnerInvolutive : Set
    contourPartnerInvolutiveEvidence : contourPartnerInvolutive

    contourPartnerDistinctOffFixedSet : Set
    contourPartnerDistinctOffFixedSetEvidence :
      contourPartnerDistinctOffFixedSet

    contourPartnerPreservesSupportAndWeight : Set
    contourPartnerPreservesSupportAndWeightEvidence :
      contourPartnerPreservesSupportAndWeight

    contourPartnerReversesOddContribution : Set
    contourPartnerReversesOddContributionEvidence :
      contourPartnerReversesOddContribution

    contourPairSumCancelsOddPart : Set
    contourPairSumCancelsOddPartEvidence :
      contourPairSumCancelsOddPart

open Gate4ExactContourPairing public

record Gate4WilsonRectangleCurvature : Set₁ where
  field
    WilsonWord Rectangle Curvature Remainder : Set

    rectangleBoundaryWordEqualsTransportedPlaquettes : Set
    rectangleBoundaryWordEqualsTransportedPlaquettesEvidence :
      rectangleBoundaryWordEqualsTransportedPlaquettes

    rectangleOrientationReversal : Set
    rectangleOrientationReversalEvidence :
      rectangleOrientationReversal

    wilsonRectangleLogEqualsCurvaturePlusRemainder : Set
    wilsonRectangleLogEqualsCurvaturePlusRemainderEvidence :
      wilsonRectangleLogEqualsCurvaturePlusRemainder

open Gate4WilsonRectangleCurvature public

record Gate4CommonPrincipalChart : Set₁ where
  field
    GroupElement LogVector : Set

    everyContourWordInsidePrincipalChart : Set
    everyContourWordInsidePrincipalChartEvidence :
      everyContourWordInsidePrincipalChart

    averagedContourInsidePrincipalChart : Set
    averagedContourInsidePrincipalChartEvidence :
      averagedContourInsidePrincipalChart

    commonBranchAgreesForEveryPairedContour : Set
    commonBranchAgreesForEveryPairedContourEvidence :
      commonBranchAgreesForEveryPairedContour

    principalLogOfAveragedContourWellDefined : Set
    principalLogOfAveragedContourWellDefinedEvidence :
      principalLogOfAveragedContourWellDefined

open Gate4CommonPrincipalChart public

record Gate4NonlinearQuadraticForcing
    (pairing : Gate4ExactContourPairing)
    (chart : Gate4CommonPrincipalChart) : Set₁ where
  field
    Field Forcing Norm Scalar : Set

    bchQuadraticRemainder : Set
    bchQuadraticRemainderEvidence : bchQuadraticRemainder

    averagedContourLinearTermCancels : Set
    averagedContourLinearTermCancelsEvidence :
      averagedContourLinearTermCancels

    contourForcingStartsQuadratically : Set
    contourForcingStartsQuadraticallyEvidence :
      contourForcingStartsQuadratically

open Gate4NonlinearQuadraticForcing public

record Gate4BackgroundGaugeSource
    (p33 : P33CoerciveInversePackage) : Set₁ where
  field
    Source GaugeDirection Constraint : Set

    sourceIsTransverse : Set
    sourceIsTransverseEvidence : sourceIsTransverse

    sourceOrthogonalToGaugeDirections : Set
    sourceOrthogonalToGaugeDirectionsEvidence :
      sourceOrthogonalToGaugeDirections

    wardIdentityForSource : Set
    wardIdentityForSourceEvidence : wardIdentityForSource

    hessianSourceCompatibility : Set
    hessianSourceCompatibilityEvidence :
      hessianSourceCompatibility

open Gate4BackgroundGaugeSource public

record Gate4GaussianDeterminant
    (p33 : P33CoerciveInversePackage) : Set₁ where
  field
    GaussianField Covariance Determinant Scalar : Set

    finiteDimensionalGaussianShift : Set
    finiteDimensionalGaussianShiftEvidence :
      finiteDimensionalGaussianShift

    gaussianCovarianceUsesP33Inverse : Set
    gaussianCovarianceUsesP33InverseEvidence :
      gaussianCovarianceUsesP33Inverse

    gaussianCovarianceBound : Set
    gaussianCovarianceBoundEvidence : gaussianCovarianceBound

    logDetRemainderBound : Set
    logDetRemainderBoundEvidence : logDetRemainderBound

    determinantRatioBound : Set
    determinantRatioBoundEvidence : determinantRatioBound

open Gate4GaussianDeterminant public

record Gate4ConnectedActivity
    {p33 : P33CoerciveInversePackage}
    (p10 : P10SuppressionAfterP33 p33) : Set₁ where
  field
    Polymer Activity WeightedNorm : Set

    connectedCumulantLocality : Set
    connectedCumulantLocalityEvidence : connectedCumulantLocality

    rOperationPreservesConnectedness : Set
    rOperationPreservesConnectednessEvidence :
      rOperationPreservesConnectedness

    rOperationWeightedNormBound : Set
    rOperationWeightedNormBoundEvidence :
      rOperationWeightedNormBound

    gate4ActivityKPSmall : Set
    gate4ActivityKPSmallEvidence : gate4ActivityKPSmall

open Gate4ConnectedActivity public

record Gate4SevenPackageSpine : Set₁ where
  field
    p33 : P33CoerciveInversePackage
    p10 : P10SuppressionAfterP33 p33

    contourPairing : Gate4ExactContourPairing
    rectangleCurvature : Gate4WilsonRectangleCurvature
    commonChart : Gate4CommonPrincipalChart
    nonlinearForcing :
      Gate4NonlinearQuadraticForcing contourPairing commonChart
    backgroundSource : Gate4BackgroundGaugeSource p33
    gaussianDeterminant : Gate4GaussianDeterminant p33
    connectedActivity : Gate4ConnectedActivity p10

    parityPackage : Parity.Gate4ParityPackage

    parityPackageUsesSameP10P33 : Set
    parityPackageUsesSameP10P33Evidence :
      parityPackageUsesSameP10P33

    allAllocatedErrorChannelsNumericallyCompatible : Set
    allAllocatedErrorChannelsNumericallyCompatibleEvidence :
      allAllocatedErrorChannelsNumericallyCompatible

    theoremBoundary : String

open Gate4SevenPackageSpine public

p33BeforeP10DependencyLevel : ProofLevel
p33BeforeP10DependencyLevel = machineChecked

p10BeforeGate4DependencyLevel : ProofLevel
p10BeforeGate4DependencyLevel = machineChecked

gate4SevenPackageDecompositionLevel : ProofLevel
gate4SevenPackageDecompositionLevel = machineChecked

p33PhysicalCoercivityAndInverseInputsLevel : ProofLevel
p33PhysicalCoercivityAndInverseInputsLevel = conditional

p10PhysicalSuppressionInputsLevel : ProofLevel
p10PhysicalSuppressionInputsLevel = conditional

gate4SevenPhysicalPackagesLevel : ProofLevel
gate4SevenPhysicalPackagesLevel = conditional
