module DASHI.Physics.Closure.NSA4CoareaStripPreimageCalculationBoundary where

-- Fail-closed boundary for the exact A4 coarea strip-preimage
-- calculation.
--
-- Scalar map:
--
--   f_n(theta1,theta2)
--     = < (theta1 + theta2) / |theta1 + theta2| , n >
--
-- on the non-antipodal product-angular domain.  The intended analytic
-- calculation records:
--
--   eta-strip slab {|f_n| <= eta}
--     -> gradient/Jacobian lower bound on regular Whitney packets
--     -> coarea slab estimate with constants uniform in n
--     -> route into NSOutputStripPreimageMeasureEstimateBoundary.
--
-- This file records the exact theorem shape and routing only.  It proves
-- no chart derivative theorem, no Jacobian lower bound, no coarea theorem,
-- no A4 theorem, no A6 leakage theorem, no Navier-Stokes Clay result, and
-- no terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4NoAngularCollapseTransferCompositeBoundary
  as NoCollapseComposite
import DASHI.Physics.Closure.NSA4SardFubiniCompositeBoundary
  as SardFubiniComposite
import DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary
  as Antipodal
import DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary
  as Pushforward
import DASHI.Physics.Closure.NSOutputGreatCircleStripSlicingBoundary
  as StripSlicing
import DASHI.Physics.Closure.NSOutputStripPreimageMeasureEstimateBoundary
  as StripPreimage
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian
import DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary
  as Sard
import DASHI.Physics.Closure.NSWhitneyFubiniDisintegrationBoundary
  as Fubini

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported A4 child surfaces.

record ImportedA4CoareaStripPreimageCalculationSupport : Set where
  field
    stripPreimageBoundary :
      StripPreimage.NSOutputStripPreimageMeasureEstimateBoundary
    stripPreimageBoundaryIsCanonical :
      stripPreimageBoundary
        ≡ StripPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    stripSlicingBoundary :
      StripSlicing.NSOutputGreatCircleStripSlicingBoundary
    stripSlicingBoundaryIsCanonical :
      stripSlicingBoundary
        ≡ StripSlicing.canonicalNSOutputGreatCircleStripSlicingBoundary
    phiJacobianBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    phiJacobianBoundaryIsCanonical :
      phiJacobianBoundary
        ≡ PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    sardFubiniCompositeBoundary :
      SardFubiniComposite.NSA4SardFubiniCompositeBoundary
    sardFubiniCompositeBoundaryIsCanonical :
      sardFubiniCompositeBoundary
        ≡ SardFubiniComposite.canonicalNSA4SardFubiniCompositeBoundary
    noAngularCollapseCompositeBoundary :
      NoCollapseComposite.NSA4NoAngularCollapseTransferCompositeBoundary
    noAngularCollapseCompositeBoundaryIsCanonical :
      noAngularCollapseCompositeBoundary
        ≡ NoCollapseComposite.canonicalNSA4NoAngularCollapseTransferCompositeBoundary
    antipodalBoundary :
      Antipodal.NSAntipodalTubeNullMassBoundary
    antipodalBoundaryIsCanonical :
      antipodalBoundary
        ≡ Antipodal.canonicalNSAntipodalTubeNullMassBoundary

    phiNormalizeSumMap :
      Pushforward.FourierOutputPhiMap
    phiNormalizeSumMapIsCanonical :
      phiNormalizeSumMap ≡ Pushforward.canonicalFourierOutputPhiMap
    nonAntipodalDomain :
      Antipodal.NormalizeSumDomainExclusion
    nonAntipodalDomainIsCanonical :
      nonAntipodalDomain ≡ Antipodal.canonicalNormalizeSumDomainExclusion
    phiDerivativeFormula :
      PhiJacobian.PhiDerivativeFormulaCarrier
    phiDerivativeFormulaIsCanonical :
      phiDerivativeFormula ≡ PhiJacobian.canonicalPhiDerivativeFormulaCarrier
    phiJacobianLowerBound :
      PhiJacobian.PhiJacobianLowerBoundCarrier
    phiJacobianLowerBoundIsCanonical :
      phiJacobianLowerBound
        ≡ PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    phiUniformConstant :
      PhiJacobian.WhitneyCapUniformConstantCarrier
    phiUniformConstantIsCanonical :
      phiUniformConstant
        ≡ PhiJacobian.canonicalWhitneyCapUniformConstantCarrier
    outputStripEstimate :
      StripPreimage.OutputStripPreimageMeasureEstimateCarrier
    outputStripEstimateIsCanonical :
      outputStripEstimate
        ≡ StripPreimage.canonicalOutputStripPreimageMeasureEstimateCarrier

    stripPreimageNowTrue :
      StripPreimage.OutputStripPreimageMeasureEstimateProved ≡ true
    stripPreimageA4NowTrue :
      StripPreimage.A4LeiRenTianFourierOutputCouplingProved ≡ true
    phiJacobianNowTrue :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ true
    phiQuantitativeJacobianNowTrue :
      PhiJacobian.PhiQuantitativeJacobianLowerBoundProved ≡ true
    stripSlicingNowTrue :
      StripSlicing.OutputGreatCircleStripSlicingProved ≡ true
    sardFubiniCompositeStillFalse :
      SardFubiniComposite.SardFubiniCompositeTheoremProved ≡ false
    noAngularCollapseCompositeStillFalse :
      NoCollapseComposite.A4NoAngularCollapseTransferTheoremProved ≡ false
    antipodalNullMassStillFalse :
      Antipodal.antipodalTubeNullMassProved ≡ false

canonicalImportedA4CoareaStripPreimageCalculationSupport :
  ImportedA4CoareaStripPreimageCalculationSupport
canonicalImportedA4CoareaStripPreimageCalculationSupport =
  record
    { stripPreimageBoundary =
        StripPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary
    ; stripPreimageBoundaryIsCanonical =
        refl
    ; stripSlicingBoundary =
        StripSlicing.canonicalNSOutputGreatCircleStripSlicingBoundary
    ; stripSlicingBoundaryIsCanonical =
        refl
    ; phiJacobianBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; phiJacobianBoundaryIsCanonical =
        refl
    ; sardFubiniCompositeBoundary =
        SardFubiniComposite.canonicalNSA4SardFubiniCompositeBoundary
    ; sardFubiniCompositeBoundaryIsCanonical =
        refl
    ; noAngularCollapseCompositeBoundary =
        NoCollapseComposite.canonicalNSA4NoAngularCollapseTransferCompositeBoundary
    ; noAngularCollapseCompositeBoundaryIsCanonical =
        refl
    ; antipodalBoundary =
        Antipodal.canonicalNSAntipodalTubeNullMassBoundary
    ; antipodalBoundaryIsCanonical =
        refl
    ; phiNormalizeSumMap =
        Pushforward.canonicalFourierOutputPhiMap
    ; phiNormalizeSumMapIsCanonical =
        refl
    ; nonAntipodalDomain =
        Antipodal.canonicalNormalizeSumDomainExclusion
    ; nonAntipodalDomainIsCanonical =
        refl
    ; phiDerivativeFormula =
        PhiJacobian.canonicalPhiDerivativeFormulaCarrier
    ; phiDerivativeFormulaIsCanonical =
        refl
    ; phiJacobianLowerBound =
        PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    ; phiJacobianLowerBoundIsCanonical =
        refl
    ; phiUniformConstant =
        PhiJacobian.canonicalWhitneyCapUniformConstantCarrier
    ; phiUniformConstantIsCanonical =
        refl
    ; outputStripEstimate =
        StripPreimage.canonicalOutputStripPreimageMeasureEstimateCarrier
    ; outputStripEstimateIsCanonical =
        refl
    ; stripPreimageNowTrue =
        refl
    ; stripPreimageA4NowTrue =
        refl
    ; phiJacobianNowTrue =
        refl
    ; phiQuantitativeJacobianNowTrue =
        refl
    ; stripSlicingNowTrue =
        refl
    ; sardFubiniCompositeStillFalse =
        refl
    ; noAngularCollapseCompositeStillFalse =
        refl
    ; antipodalNullMassStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Exact scalar coarea calculation carriers.

data OutputNormalCarrier : Set where
  unitOutputNormalForGreatCircle :
    StripSlicing.GreatCircleCarrier →
    OutputNormalCarrier

data NonAntipodalCoareaDomainCarrier : Set where
  thetaPairsWithNormalizeSumDefinedAndTubeDiscarded :
    Pushforward.InputAngularPairCarrier →
    Antipodal.AntipodalTubeCarrier →
    Antipodal.NormalizeSumDomainExclusion →
    NonAntipodalCoareaDomainCarrier

data NormalizedSumOutputCarrier : Set where
  uEqualsThetaOnePlusThetaTwoDividedByItsNorm :
    Pushforward.FourierOutputPhiMap →
    NonAntipodalCoareaDomainCarrier →
    NormalizedSumOutputCarrier

data ScalarA4CoareaFunctionCarrier : Set where
  fThetaOneThetaTwoEqualsNormalizedSumDotNormal :
    NormalizedSumOutputCarrier →
    OutputNormalCarrier →
    ScalarA4CoareaFunctionCarrier

data ExactGradientFormulaCarrier : Set where
  gradientOfDotNormalizeSumIsProjectedNormalOverSumNorm :
    ScalarA4CoareaFunctionCarrier →
    PhiJacobian.PhiDerivativeFormulaCarrier →
    ExactGradientFormulaCarrier

data TangentialJacobianLowerBoundCarrier : Set where
  coareaJacobianBoundedBelowOnRegularNonAntipodalPackets :
    ExactGradientFormulaCarrier →
    PhiJacobian.PhiChartRankCarrier →
    PhiJacobian.PhiJacobianLowerBoundCarrier →
    Sard.RegularValueCarrier →
    TangentialJacobianLowerBoundCarrier

data EtaStripSlabCarrier : Set where
  etaSlabWhereAbsNormalizedSumDotNormalIsAtMostEta :
    Nat →
    ScalarA4CoareaFunctionCarrier →
    StripSlicing.OutputStripWidthCarrier →
    EtaStripSlabCarrier

data CoareaLevelSetMeasureCarrier : Set where
  levelSetsIntegratedAcrossMinusEtaToEta :
    EtaStripSlabCarrier →
    TangentialJacobianLowerBoundCarrier →
    Fubini.PhysicalPacketDisintegrationCarrier →
    CoareaLevelSetMeasureCarrier

data UniformInNormalConstantCarrier : Set where
  constantsDependOnSeparationPacketsAndOverlapNotNormal :
    OutputNormalCarrier →
    PhiJacobian.WhitneyCapUniformConstantCarrier →
    StripSlicing.StripPreimageMeasureEstimateCarrier →
    UniformInNormalConstantCarrier

data EtaStripCoareaSlabEstimateCarrier : Set where
  etaStripSlabMeasureControlledByEtaOverJacobianUniformlyInNormal :
    CoareaLevelSetMeasureCarrier →
    UniformInNormalConstantCarrier →
    StripPreimage.StripWidthJacobianBudgetCarrier →
    StripPreimage.NullExceptionalBudgetCarrier →
    EtaStripCoareaSlabEstimateCarrier

data CoareaRouteToOutputStripPreimageBoundary : Set where
  coareaSlabEstimateRoutesToNSOutputStripPreimageMeasureEstimateBoundary :
    EtaStripCoareaSlabEstimateCarrier →
    StripPreimage.OutputStripPreimageMeasureEstimateCarrier →
    StripPreimage.A4OutputStripPreimageEstimateConsumer →
    StripPreimage.NSOutputStripPreimageMeasureEstimateBoundary →
    CoareaRouteToOutputStripPreimageBoundary

data A4CoareaStripPreimageCalculationTarget : Set where
  exactNormalizeSumDotNormalCoareaCalculationRecorded :
    ImportedA4CoareaStripPreimageCalculationSupport →
    NonAntipodalCoareaDomainCarrier →
    ScalarA4CoareaFunctionCarrier →
    ExactGradientFormulaCarrier →
    TangentialJacobianLowerBoundCarrier →
    EtaStripSlabCarrier →
    CoareaLevelSetMeasureCarrier →
    UniformInNormalConstantCarrier →
    EtaStripCoareaSlabEstimateCarrier →
    CoareaRouteToOutputStripPreimageBoundary →
    A4CoareaStripPreimageCalculationTarget

canonicalOutputNormalCarrier :
  OutputNormalCarrier
canonicalOutputNormalCarrier =
  unitOutputNormalForGreatCircle
    StripSlicing.canonicalGreatCircleCarrier

canonicalNonAntipodalCoareaDomainCarrier :
  NonAntipodalCoareaDomainCarrier
canonicalNonAntipodalCoareaDomainCarrier =
  thetaPairsWithNormalizeSumDefinedAndTubeDiscarded
    Pushforward.canonicalInputAngularPairCarrier
    Antipodal.canonicalAntipodalTubeCarrier
    Antipodal.canonicalNormalizeSumDomainExclusion

canonicalNormalizedSumOutputCarrier :
  NormalizedSumOutputCarrier
canonicalNormalizedSumOutputCarrier =
  uEqualsThetaOnePlusThetaTwoDividedByItsNorm
    Pushforward.canonicalFourierOutputPhiMap
    canonicalNonAntipodalCoareaDomainCarrier

canonicalScalarA4CoareaFunctionCarrier :
  ScalarA4CoareaFunctionCarrier
canonicalScalarA4CoareaFunctionCarrier =
  fThetaOneThetaTwoEqualsNormalizedSumDotNormal
    canonicalNormalizedSumOutputCarrier
    canonicalOutputNormalCarrier

canonicalExactGradientFormulaCarrier :
  ExactGradientFormulaCarrier
canonicalExactGradientFormulaCarrier =
  gradientOfDotNormalizeSumIsProjectedNormalOverSumNorm
    canonicalScalarA4CoareaFunctionCarrier
    PhiJacobian.canonicalPhiDerivativeFormulaCarrier

canonicalTangentialJacobianLowerBoundCarrier :
  TangentialJacobianLowerBoundCarrier
canonicalTangentialJacobianLowerBoundCarrier =
  coareaJacobianBoundedBelowOnRegularNonAntipodalPackets
    canonicalExactGradientFormulaCarrier
    PhiJacobian.canonicalPhiChartRankCarrier
    PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    Sard.canonicalRegularValueCarrier

canonicalEtaStripSlabCarrier :
  EtaStripSlabCarrier
canonicalEtaStripSlabCarrier =
  etaSlabWhereAbsNormalizedSumDotNormalIsAtMostEta
    (suc zero)
    canonicalScalarA4CoareaFunctionCarrier
    StripSlicing.canonicalOutputStripWidthCarrier

canonicalCoareaLevelSetMeasureCarrier :
  CoareaLevelSetMeasureCarrier
canonicalCoareaLevelSetMeasureCarrier =
  levelSetsIntegratedAcrossMinusEtaToEta
    canonicalEtaStripSlabCarrier
    canonicalTangentialJacobianLowerBoundCarrier
    Fubini.canonicalPhysicalPacketDisintegrationCarrier

canonicalUniformInNormalConstantCarrier :
  UniformInNormalConstantCarrier
canonicalUniformInNormalConstantCarrier =
  constantsDependOnSeparationPacketsAndOverlapNotNormal
    canonicalOutputNormalCarrier
    PhiJacobian.canonicalWhitneyCapUniformConstantCarrier
    StripSlicing.canonicalStripPreimageMeasureEstimateCarrier

canonicalEtaStripCoareaSlabEstimateCarrier :
  EtaStripCoareaSlabEstimateCarrier
canonicalEtaStripCoareaSlabEstimateCarrier =
  etaStripSlabMeasureControlledByEtaOverJacobianUniformlyInNormal
    canonicalCoareaLevelSetMeasureCarrier
    canonicalUniformInNormalConstantCarrier
    StripPreimage.canonicalStripWidthJacobianBudgetCarrier
    StripPreimage.canonicalNullExceptionalBudgetCarrier

canonicalCoareaRouteToOutputStripPreimageBoundary :
  CoareaRouteToOutputStripPreimageBoundary
canonicalCoareaRouteToOutputStripPreimageBoundary =
  coareaSlabEstimateRoutesToNSOutputStripPreimageMeasureEstimateBoundary
    canonicalEtaStripCoareaSlabEstimateCarrier
    StripPreimage.canonicalOutputStripPreimageMeasureEstimateCarrier
    StripPreimage.canonicalA4OutputStripPreimageEstimateConsumer
    StripPreimage.canonicalNSOutputStripPreimageMeasureEstimateBoundary

canonicalA4CoareaStripPreimageCalculationTarget :
  A4CoareaStripPreimageCalculationTarget
canonicalA4CoareaStripPreimageCalculationTarget =
  exactNormalizeSumDotNormalCoareaCalculationRecorded
    canonicalImportedA4CoareaStripPreimageCalculationSupport
    canonicalNonAntipodalCoareaDomainCarrier
    canonicalScalarA4CoareaFunctionCarrier
    canonicalExactGradientFormulaCarrier
    canonicalTangentialJacobianLowerBoundCarrier
    canonicalEtaStripSlabCarrier
    canonicalCoareaLevelSetMeasureCarrier
    canonicalUniformInNormalConstantCarrier
    canonicalEtaStripCoareaSlabEstimateCarrier
    canonicalCoareaRouteToOutputStripPreimageBoundary

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data A4CoareaStripPreimageCalculationObligation : Set where
  fixUnitOutputNormalAndGreatCircle :
    A4CoareaStripPreimageCalculationObligation
  restrictToNonAntipodalNormalizeSumDomain :
    A4CoareaStripPreimageCalculationObligation
  defineScalarFunctionAsNormalizedSumDotNormal :
    A4CoareaStripPreimageCalculationObligation
  computeGradientAsProjectedNormalOverNormThetaSum :
    A4CoareaStripPreimageCalculationObligation
  proveTangentialJacobianLowerBoundOnRegularPackets :
    A4CoareaStripPreimageCalculationObligation
  identifyEtaStripAsCoareaSlab :
    A4CoareaStripPreimageCalculationObligation
  applyCoareaFormulaAcrossMinusEtaToEta :
    A4CoareaStripPreimageCalculationObligation
  keepConstantsUniformInOutputNormal :
    A4CoareaStripPreimageCalculationObligation
  routeAntipodalCriticalRankDropAndPacketBoundaryExceptions :
    A4CoareaStripPreimageCalculationObligation
  feedCoareaSlabIntoOutputStripPreimageMeasureEstimate :
    A4CoareaStripPreimageCalculationObligation
  keepAnalyticTheoremA4A6NSClayAndTerminalPromotionFalse :
    A4CoareaStripPreimageCalculationObligation

canonicalA4CoareaStripPreimageCalculationObligations :
  List A4CoareaStripPreimageCalculationObligation
canonicalA4CoareaStripPreimageCalculationObligations =
  fixUnitOutputNormalAndGreatCircle
  ∷ restrictToNonAntipodalNormalizeSumDomain
  ∷ defineScalarFunctionAsNormalizedSumDotNormal
  ∷ computeGradientAsProjectedNormalOverNormThetaSum
  ∷ proveTangentialJacobianLowerBoundOnRegularPackets
  ∷ identifyEtaStripAsCoareaSlab
  ∷ applyCoareaFormulaAcrossMinusEtaToEta
  ∷ keepConstantsUniformInOutputNormal
  ∷ routeAntipodalCriticalRankDropAndPacketBoundaryExceptions
  ∷ feedCoareaSlabIntoOutputStripPreimageMeasureEstimate
  ∷ keepAnalyticTheoremA4A6NSClayAndTerminalPromotionFalse
  ∷ []

A4CoareaStripPreimageCalculationObligationCount : Nat
A4CoareaStripPreimageCalculationObligationCount =
  listLength canonicalA4CoareaStripPreimageCalculationObligations

A4CoareaStripPreimageCalculationObligationCountIs11 :
  A4CoareaStripPreimageCalculationObligationCount ≡ 11
A4CoareaStripPreimageCalculationObligationCountIs11 =
  refl

data A4CoareaStripPreimageCalculationBlocker : Set where
  missingExactChartGradientProof :
    A4CoareaStripPreimageCalculationBlocker
  missingTangentialJacobianLowerBound :
    A4CoareaStripPreimageCalculationBlocker
  missingUniformInNormalConstantProof :
    A4CoareaStripPreimageCalculationBlocker
  missingCoareaSlabMeasureProof :
    A4CoareaStripPreimageCalculationBlocker
  missingAntipodalCriticalRankDropExceptionalRouting :
    A4CoareaStripPreimageCalculationBlocker
  missingOutputStripPreimageMeasurePromotion :
    A4CoareaStripPreimageCalculationBlocker
  missingA4Promotion :
    A4CoareaStripPreimageCalculationBlocker
  missingA6Promotion :
    A4CoareaStripPreimageCalculationBlocker
  missingNSClayPromotion :
    A4CoareaStripPreimageCalculationBlocker

canonicalA4CoareaStripPreimageCalculationBlockers :
  List A4CoareaStripPreimageCalculationBlocker
canonicalA4CoareaStripPreimageCalculationBlockers =
  missingExactChartGradientProof
  ∷ missingTangentialJacobianLowerBound
  ∷ missingUniformInNormalConstantProof
  ∷ missingCoareaSlabMeasureProof
  ∷ missingAntipodalCriticalRankDropExceptionalRouting
  ∷ missingOutputStripPreimageMeasurePromotion
  ∷ missingA4Promotion
  ∷ missingA6Promotion
  ∷ missingNSClayPromotion
  ∷ []

A4CoareaStripPreimageCalculationBlockerCount : Nat
A4CoareaStripPreimageCalculationBlockerCount =
  listLength canonicalA4CoareaStripPreimageCalculationBlockers

A4CoareaStripPreimageCalculationBlockerCountIs9 :
  A4CoareaStripPreimageCalculationBlockerCount ≡ 9
A4CoareaStripPreimageCalculationBlockerCountIs9 =
  refl

data A4CoareaStripPreimageCalculationStatusRow : Set where
  boundaryRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  A4ChildSurfacesImportedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  nonAntipodalDomainRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  scalarFunctionRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  gradientFormulaRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  jacobianLowerBoundTargetRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  etaStripCoareaSlabRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  uniformInNormalConstantsRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  routeToOutputStripPreimageBoundaryRecordedStatus :
    A4CoareaStripPreimageCalculationStatusRow
  allAnalyticTheoremAndPromotionFlagsFalseStatus :
    A4CoareaStripPreimageCalculationStatusRow

canonicalA4CoareaStripPreimageCalculationStatusRows :
  List A4CoareaStripPreimageCalculationStatusRow
canonicalA4CoareaStripPreimageCalculationStatusRows =
  boundaryRecordedStatus
  ∷ A4ChildSurfacesImportedStatus
  ∷ nonAntipodalDomainRecordedStatus
  ∷ scalarFunctionRecordedStatus
  ∷ gradientFormulaRecordedStatus
  ∷ jacobianLowerBoundTargetRecordedStatus
  ∷ etaStripCoareaSlabRecordedStatus
  ∷ uniformInNormalConstantsRecordedStatus
  ∷ routeToOutputStripPreimageBoundaryRecordedStatus
  ∷ allAnalyticTheoremAndPromotionFlagsFalseStatus
  ∷ []

A4CoareaStripPreimageCalculationStatusRowCount : Nat
A4CoareaStripPreimageCalculationStatusRowCount =
  listLength canonicalA4CoareaStripPreimageCalculationStatusRows

A4CoareaStripPreimageCalculationStatusRowCountIs10 :
  A4CoareaStripPreimageCalculationStatusRowCount ≡ 10
A4CoareaStripPreimageCalculationStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data A4CoareaStripPreimageCalculationPromotion : Set where

A4CoareaStripPreimageCalculationPromotionImpossibleHere :
  A4CoareaStripPreimageCalculationPromotion →
  ⊥
A4CoareaStripPreimageCalculationPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSA4CoareaStripPreimageCalculationBoundaryRecorded : Bool
NSA4CoareaStripPreimageCalculationBoundaryRecorded =
  true

nonAntipodalNormalizeSumDomainRecorded : Bool
nonAntipodalNormalizeSumDomainRecorded =
  true

scalarNormalizeSumDotNormalFunctionRecorded : Bool
scalarNormalizeSumDotNormalFunctionRecorded =
  true

exactGradientFormulaRecorded : Bool
exactGradientFormulaRecorded =
  true

tangentialJacobianLowerBoundTargetRecorded : Bool
tangentialJacobianLowerBoundTargetRecorded =
  true

etaStripCoareaSlabRecorded : Bool
etaStripCoareaSlabRecorded =
  true

uniformInNormalConstantsRecorded : Bool
uniformInNormalConstantsRecorded =
  true

routeToNSOutputStripPreimageMeasureEstimateBoundaryRecorded : Bool
routeToNSOutputStripPreimageMeasureEstimateBoundaryRecorded =
  true

exactGradientFormulaProved : Bool
exactGradientFormulaProved =
  false

tangentialJacobianLowerBoundProved : Bool
tangentialJacobianLowerBoundProved =
  false

coareaSlabMeasureEstimateProved : Bool
coareaSlabMeasureEstimateProved =
  false

uniformInNormalConstantsProved : Bool
uniformInNormalConstantsProved =
  false

analyticA4CoareaStripPreimageTheoremProved : Bool
analyticA4CoareaStripPreimageTheoremProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

A6TriadicCompensatedLeakageIdentityProved : Bool
A6TriadicCompensatedLeakageIdentityProved =
  false

fullLocalDefectMonotonicity : Bool
fullLocalDefectMonotonicity =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSA4CoareaStripPreimageCalculationBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsNonAntipodalNormalizeSumDomain :
  nonAntipodalNormalizeSumDomainRecorded ≡ true
recordsNonAntipodalNormalizeSumDomain =
  refl

recordsScalarNormalizeSumDotNormalFunction :
  scalarNormalizeSumDotNormalFunctionRecorded ≡ true
recordsScalarNormalizeSumDotNormalFunction =
  refl

recordsExactGradientFormula :
  exactGradientFormulaRecorded ≡ true
recordsExactGradientFormula =
  refl

recordsTangentialJacobianLowerBoundTarget :
  tangentialJacobianLowerBoundTargetRecorded ≡ true
recordsTangentialJacobianLowerBoundTarget =
  refl

recordsEtaStripCoareaSlab :
  etaStripCoareaSlabRecorded ≡ true
recordsEtaStripCoareaSlab =
  refl

recordsUniformInNormalConstants :
  uniformInNormalConstantsRecorded ≡ true
recordsUniformInNormalConstants =
  refl

recordsRouteToNSOutputStripPreimageMeasureEstimateBoundary :
  routeToNSOutputStripPreimageMeasureEstimateBoundaryRecorded ≡ true
recordsRouteToNSOutputStripPreimageMeasureEstimateBoundary =
  refl

keepsExactGradientFormulaProvedFalse :
  exactGradientFormulaProved ≡ false
keepsExactGradientFormulaProvedFalse =
  refl

keepsTangentialJacobianLowerBoundFalse :
  tangentialJacobianLowerBoundProved ≡ false
keepsTangentialJacobianLowerBoundFalse =
  refl

keepsCoareaSlabMeasureEstimateFalse :
  coareaSlabMeasureEstimateProved ≡ false
keepsCoareaSlabMeasureEstimateFalse =
  refl

keepsUniformInNormalConstantsFalse :
  uniformInNormalConstantsProved ≡ false
keepsUniformInNormalConstantsFalse =
  refl

keepsAnalyticA4CoareaStripPreimageTheoremFalse :
  analyticA4CoareaStripPreimageTheoremProved ≡ false
keepsAnalyticA4CoareaStripPreimageTheoremFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingFalse =
  refl

keepsA6TriadicCompensatedLeakageIdentityFalse :
  A6TriadicCompensatedLeakageIdentityProved ≡ false
keepsA6TriadicCompensatedLeakageIdentityFalse =
  refl

keepsFullLocalDefectMonotonicityFalse :
  fullLocalDefectMonotonicity ≡ false
keepsFullLocalDefectMonotonicityFalse =
  refl

keepsFullClayNSSolvedFalse :
  fullClayNSSolved ≡ false
keepsFullClayNSSolvedFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F.

organizationString : String
organizationString =
  "O: Isolate the A4 scalar coarea calculation for f_n(theta1,theta2)=<normalize(theta1+theta2),n> as a boundary feeding the existing output-strip preimage estimate."

requirementString : String
requirementString =
  "R: Record non-antipodal domain, gradient/Jacobian lower bound, eta-strip coarea slab, constants uniform in n, and route to NSOutputStripPreimageMeasureEstimateBoundary."

codeArtifactString : String
codeArtifactString =
  "C: DASHI.Physics.Closure.NSA4CoareaStripPreimageCalculationBoundary exports canonical carriers, target, obligations, blockers, status rows, and fail-closed flags."

stateString : String
stateString =
  "S: The boundary is recorded only; exact gradient proof, Jacobian proof, coarea slab proof, A4, A6, NS Clay, and terminal promotion remain false."

latticeString : String
latticeString =
  "L: non-antipodal pair -> normalized sum -> dot-normal scalar f_n -> gradient/Jacobian lower bound -> eta slab -> coarea level-set integration -> strip-preimage route."

proposalString : String
proposalString =
  "P: Discharge blockers by proving the chart gradient, uniform packet Jacobian lower bound, and coarea slab estimate before enabling any A4 consumer."

governanceString : String
governanceString =
  "G: The module imports child A4 surfaces but consumes them as fail-closed contracts; no analytic theorem flag or promotion flag is raised."

failureString : String
failureString =
  "F: Remaining failures are the missing analytic gradient proof, lower bound, uniform-in-n constants, exceptional routing, coarea estimate, A4/A6, and Clay promotion."

record A4CoareaStripPreimageCalculationBoundaryReceipt : Set where
  field
    importedSupport :
      ImportedA4CoareaStripPreimageCalculationSupport
    target :
      A4CoareaStripPreimageCalculationTarget
    obligations :
      List A4CoareaStripPreimageCalculationObligation
    blockers :
      List A4CoareaStripPreimageCalculationBlocker
    statusRows :
      List A4CoareaStripPreimageCalculationStatusRow
    boundaryRecordedTrue :
      NSA4CoareaStripPreimageCalculationBoundaryRecorded ≡ true
    nonAntipodalDomainRecordedTrue :
      nonAntipodalNormalizeSumDomainRecorded ≡ true
    scalarFunctionRecordedTrue :
      scalarNormalizeSumDotNormalFunctionRecorded ≡ true
    gradientFormulaRecordedTrue :
      exactGradientFormulaRecorded ≡ true
    jacobianLowerBoundTargetRecordedTrue :
      tangentialJacobianLowerBoundTargetRecorded ≡ true
    etaStripCoareaSlabRecordedTrue :
      etaStripCoareaSlabRecorded ≡ true
    uniformInNormalConstantsRecordedTrue :
      uniformInNormalConstantsRecorded ≡ true
    routeToStripPreimageRecordedTrue :
      routeToNSOutputStripPreimageMeasureEstimateBoundaryRecorded ≡ true
    analyticTheoremStillFalse :
      analyticA4CoareaStripPreimageTheoremProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    NSClayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false
    O :
      String
    R :
      String
    C :
      String
    S :
      String
    L :
      String
    P :
      String
    G :
      String
    F :
      String

canonicalA4CoareaStripPreimageCalculationBoundaryReceipt :
  A4CoareaStripPreimageCalculationBoundaryReceipt
canonicalA4CoareaStripPreimageCalculationBoundaryReceipt =
  record
    { importedSupport =
        canonicalImportedA4CoareaStripPreimageCalculationSupport
    ; target =
        canonicalA4CoareaStripPreimageCalculationTarget
    ; obligations =
        canonicalA4CoareaStripPreimageCalculationObligations
    ; blockers =
        canonicalA4CoareaStripPreimageCalculationBlockers
    ; statusRows =
        canonicalA4CoareaStripPreimageCalculationStatusRows
    ; boundaryRecordedTrue =
        refl
    ; nonAntipodalDomainRecordedTrue =
        refl
    ; scalarFunctionRecordedTrue =
        refl
    ; gradientFormulaRecordedTrue =
        refl
    ; jacobianLowerBoundTargetRecordedTrue =
        refl
    ; etaStripCoareaSlabRecordedTrue =
        refl
    ; uniformInNormalConstantsRecordedTrue =
        refl
    ; routeToStripPreimageRecordedTrue =
        refl
    ; analyticTheoremStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; NSClayStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    ; O =
        organizationString
    ; R =
        requirementString
    ; C =
        codeArtifactString
    ; S =
        stateString
    ; L =
        latticeString
    ; P =
        proposalString
    ; G =
        governanceString
    ; F =
        failureString
    }

record NSA4CoareaStripPreimageCalculationBoundary : Set where
  field
    receipt :
      A4CoareaStripPreimageCalculationBoundaryReceipt
    target :
      A4CoareaStripPreimageCalculationTarget
    route :
      CoareaRouteToOutputStripPreimageBoundary
    theoremStillFalse :
      analyticA4CoareaStripPreimageTheoremProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    clayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false

canonicalNSA4CoareaStripPreimageCalculationBoundary :
  NSA4CoareaStripPreimageCalculationBoundary
canonicalNSA4CoareaStripPreimageCalculationBoundary =
  record
    { receipt =
        canonicalA4CoareaStripPreimageCalculationBoundaryReceipt
    ; target =
        canonicalA4CoareaStripPreimageCalculationTarget
    ; route =
        canonicalCoareaRouteToOutputStripPreimageBoundary
    ; theoremStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; clayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }
