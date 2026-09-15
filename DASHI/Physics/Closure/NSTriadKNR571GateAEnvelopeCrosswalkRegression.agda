module DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkRegression where

-- RED/GREEN contract for the post-#920 Gate-A tranche.
-- Production must preserve the merged R571 paired-second-moment carrier,
-- reuse existing donors for A1/G2/G1, isolate A2 as the radial-curvature leaf,
-- record the theorem-bearing Lean A1/A2 receipts without fabricating an Agda
-- sample transport, expose the local Hermitian G0' weld, and must not promote
-- G1/G2, R568, or a Clay endpoint.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureBoundaryExact as A2
import DASHI.Physics.Closure.NSTriadKNR571RadialCurvatureSquareGapExact as A2Square
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as CenteredShift
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftRadiusDoublingExact as RadiusDouble
import DASHI.Physics.Closure.NSTriadKNR571CenteredAlignedComplementExact as Aligned
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialDenominatorOrderExact as Denominator
import DASHI.Physics.Closure.NSTriadKNR571CenteredRadialProductBridgeExact as ProductBridge

preferredLinearizationClosed :
  GateA.r571GateAPreferredLinearizationClosed ≡ true
preferredLinearizationClosed = refl

existingA1GeometryDonorRetained :
  GateA.r571GateAA1ReverseTriangleDonorLocated ≡ true
existingA1GeometryDonorRetained = refl

leanA1TheoremReceiptVisible :
  GateA.r571GateAA1LeanTheoremReceiptObserved ≡ true
leanA1TheoremReceiptVisible = refl

leanA2TheoremReceiptVisible :
  GateA.r571GateAA2LeanTheoremReceiptObserved ≡ true
leanA2TheoremReceiptVisible = refl

leanReceiptDoesNotCreateAgdaA1SampleWeld :
  GateA.r571GateAA1AgdaSampleTransportObserved ≡ false
leanReceiptDoesNotCreateAgdaA1SampleWeld = refl

leanReceiptDoesNotCreateAgdaA2SampleWeld :
  GateA.r571GateAA2AgdaSampleTransportObserved ≡ false
leanReceiptDoesNotCreateAgdaA2SampleWeld = refl

localHermitianG0WeldClosed :
  GateA.r571GateAG0HermitianScalarizedPairClosed ≡ true
localHermitianG0WeldClosed = refl

globalScalarStateStillNotRequired :
  GateA.r571GateAGlobalPhysicalScalarStateRequired ≡ false
globalScalarStateStillNotRequired = refl

existingG2PathDonorRetained :
  GateA.r571GateAG2FinitePathDonorLocated ≡ true
existingG2PathDonorRetained = refl

existingG1ModalEnvelopeDonorRetained :
  GateA.r571GateAG1ModalEnergyDonorLocated ≡ true
existingG1ModalEnvelopeDonorRetained = refl

stateSideEnvelopeStillOpen :
  GateA.r571GateAStateDerivativeEnvelopeClosed ≡ false
stateSideEnvelopeStillOpen = refl

radialCurvatureIsOnlyNewLocalLeaf :
  A2.r571A2RadialCurvatureIsolated ≡ true
radialCurvatureIsOnlyNewLocalLeaf = refl

radialCurvatureSquareGapRationalizationClosed :
  A2Square.r571A2CenteredRadiusDefectSquareGapRationalized ≡ true
radialCurvatureSquareGapRationalizationClosed = refl

radialCurvatureTriangleExcessFactorizationClosed :
  A2Square.r571A2TriangleExcessPolarizationFactorizationClosed ≡ true
radialCurvatureTriangleExcessFactorizationClosed = refl

centeredShiftModeSumIsDoubledCenterClosed :
  CenteredShift.r571A2CenteredShiftModeSumClosed ≡ true
centeredShiftModeSumIsDoubledCenterClosed = refl

centeredShiftSquaredOutputScalingClosed :
  CenteredShift.r571A2CenteredShiftSquaredOutputScalingClosed ≡ true
centeredShiftSquaredOutputScalingClosed = refl

centeredShiftAlignedPluckerScalingClosed :
  CenteredShift.r571A2CenteredShiftPluckerScalingClosed ≡ true
centeredShiftAlignedPluckerScalingClosed = refl

centeredShiftScalarRadiusDoublingClosed :
  RadiusDouble.r571A2CenteredShiftScalarRadiusDoublingClosed ≡ true
centeredShiftScalarRadiusDoublingClosed = refl

centeredShiftRadiusDoublingUsesSquareRootAxiom :
  RadiusDouble.r571A2CenteredShiftRadiusDoublingUsesSquareRootAxiom ≡ false
centeredShiftRadiusDoublingUsesSquareRootAxiom = refl

literalAlignedComplementIdentityClosed :
  Aligned.r571A2LiteralAlignedComplementIdentityClosed ≡ true
literalAlignedComplementIdentityClosed = refl

centeredAlignedAngularSecondMomentPaymentClosed :
  Aligned.r571A2CenteredAlignedAngularSecondMomentPaymentClosed ≡ true
centeredAlignedAngularSecondMomentPaymentClosed = refl

divisionFreeDenominatorCompilerClosed :
  Denominator.r571A2DivisionFreeDenominatorCompilerClosed ≡ true
divisionFreeDenominatorCompilerClosed = refl

denominatorRequiresAnnularPositiveLowerBound :
  Denominator.r571A2RequiresAnnularPositiveLowerBound ≡ false
denominatorRequiresAnnularPositiveLowerBound = refl

denominatorRequiresRadiusDivision :
  Denominator.r571A2RequiresRadiusDivision ≡ false
denominatorRequiresRadiusDivision = refl

literalCenteredProductBridgeClosed :
  ProductBridge.r571A2LiteralCenteredProductBridgeClosed ≡ true
literalCenteredProductBridgeClosed = refl

divisionFreeRadialCurvaturePaymentClosed :
  ProductBridge.r571A2DivisionFreeRadialCurvaturePaymentClosed ≡ true
divisionFreeRadialCurvaturePaymentClosed = refl

orderedRadialDenominatorLeafPaid :
  A2.r571A2OrderedRadialDenominatorPaymentClosed ≡ true
orderedRadialDenominatorLeafPaid = refl

radialCurvatureUsesExistingGapProductDonor :
  A2Square.r571A2R127SquareGapAlgebraReused ≡ true
radialCurvatureUsesExistingGapProductDonor = refl

-- Deliberately still false: the local centered curvature is now paid, but its
-- exact sign/absolute-value/stepMagnitude transport into the Gate-A sample has
-- not yet been written.
radialCurvatureSampleTransportStillOpen :
  A2.r571A2UniformCurvatureEstimateClosed ≡ false
radialCurvatureSampleTransportStillOpen = refl

r568StillOpen :
  GateA.r571GateAClosesR568 ≡ false
r568StillOpen = refl
