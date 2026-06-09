module DASHI.Physics.Closure.NSA4DerivativeJacobianLowerBoundCompositeBoundary where

-- NS A4 composite boundary: derivative formula plus Jacobian lower-bound
-- route into the coarea strip-preimage calculation.
--
-- This module is the Worker-1 composite for the local analytic segment:
--
--   local chart formula for f_n(theta1,theta2)
--     -> derivative of normalize(theta1 + theta2)
--     -> scalar gradient/rank noncritical condition
--     -> Phi-Jacobian lower bound away from antipodal/rank-drop sets
--     -> tangential coarea Jacobian lower bound
--     -> eta-strip slab estimate.
--
-- It composes only the three assigned child surfaces:
--   * NSA4GradientFormulaLocalChartBoundary
--   * NSPhiJacobianLowerBoundBoundary
--   * NSA4CoareaStripPreimageCalculationBoundary
--
-- It proves no derivative theorem, no quantitative Jacobian theorem, no
-- coarea theorem, no A4 theorem, no A6 theorem, no Navier-Stokes Clay
-- result, and no terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4CoareaStripPreimageCalculationBoundary
  as Coarea
import DASHI.Physics.Closure.NSA4GradientFormulaLocalChartBoundary
  as Gradient
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support.

record ImportedDerivativeJacobianLowerBoundCompositeSupport : Set where
  field
    gradientBoundary :
      Gradient.NSA4GradientFormulaLocalChartBoundary
    gradientBoundaryIsCanonical :
      gradientBoundary
        ≡ Gradient.canonicalNSA4GradientFormulaLocalChartBoundary

    phiJacobianBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    phiJacobianBoundaryIsCanonical :
      phiJacobianBoundary
        ≡ PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary

    coareaBoundary :
      Coarea.NSA4CoareaStripPreimageCalculationBoundary
    coareaBoundaryIsCanonical :
      coareaBoundary
        ≡ Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary

    gradientImportedSupport :
      Gradient.ImportedA4GradientFormulaLocalChartSupport
    gradientImportedSupportIsCanonical :
      gradientImportedSupport
        ≡ Gradient.canonicalImportedA4GradientFormulaLocalChartSupport

    gradientTarget :
      Gradient.A4GradientFormulaLocalChartTarget
    gradientTargetIsCanonical :
      gradientTarget ≡ Gradient.canonicalA4GradientFormulaLocalChartTarget

    localChartRoute :
      Gradient.LocalChartGradientToCoareaRoute
    localChartRouteIsCanonical :
      localChartRoute ≡ Gradient.canonicalLocalChartGradientToCoareaRoute

    phiDerivativeFormula :
      PhiJacobian.PhiDerivativeFormulaCarrier
    phiDerivativeFormulaIsCanonical :
      phiDerivativeFormula
        ≡ PhiJacobian.canonicalPhiDerivativeFormulaCarrier

    phiRankCarrier :
      PhiJacobian.PhiChartRankCarrier
    phiRankCarrierIsCanonical :
      phiRankCarrier ≡ PhiJacobian.canonicalPhiChartRankCarrier

    phiJacobianLowerBound :
      PhiJacobian.PhiJacobianLowerBoundCarrier
    phiJacobianLowerBoundIsCanonical :
      phiJacobianLowerBound
        ≡ PhiJacobian.canonicalPhiJacobianLowerBoundCarrier

    phiDegenerateTriadExclusion :
      PhiJacobian.DegenerateTriadExclusionCarrier
    phiDegenerateTriadExclusionIsCanonical :
      phiDegenerateTriadExclusion
        ≡ PhiJacobian.canonicalDegenerateTriadExclusionCarrier

    phiBudgetAbsorption :
      PhiJacobian.DegenerateTriadBudgetAbsorptionCarrier
    phiBudgetAbsorptionIsCanonical :
      phiBudgetAbsorption
        ≡ PhiJacobian.canonicalDegenerateTriadBudgetAbsorptionCarrier

    phiCapUniformConstant :
      PhiJacobian.WhitneyCapUniformConstantCarrier
    phiCapUniformConstantIsCanonical :
      phiCapUniformConstant
        ≡ PhiJacobian.canonicalWhitneyCapUniformConstantCarrier

    phiTarget :
      PhiJacobian.PhiJacobianLowerBoundTarget
    phiTargetIsCanonical :
      phiTarget ≡ PhiJacobian.canonicalPhiJacobianLowerBoundTarget

    coareaExactGradient :
      Coarea.ExactGradientFormulaCarrier
    coareaExactGradientIsCanonical :
      coareaExactGradient
        ≡ Coarea.canonicalExactGradientFormulaCarrier

    coareaTangentialJacobian :
      Coarea.TangentialJacobianLowerBoundCarrier
    coareaTangentialJacobianIsCanonical :
      coareaTangentialJacobian
        ≡ Coarea.canonicalTangentialJacobianLowerBoundCarrier

    coareaEtaStripSlab :
      Coarea.EtaStripSlabCarrier
    coareaEtaStripSlabIsCanonical :
      coareaEtaStripSlab ≡ Coarea.canonicalEtaStripSlabCarrier

    coareaLevelSetMeasure :
      Coarea.CoareaLevelSetMeasureCarrier
    coareaLevelSetMeasureIsCanonical :
      coareaLevelSetMeasure
        ≡ Coarea.canonicalCoareaLevelSetMeasureCarrier

    coareaSlabEstimate :
      Coarea.EtaStripCoareaSlabEstimateCarrier
    coareaSlabEstimateIsCanonical :
      coareaSlabEstimate
        ≡ Coarea.canonicalEtaStripCoareaSlabEstimateCarrier

    coareaRoute :
      Coarea.CoareaRouteToOutputStripPreimageBoundary
    coareaRouteIsCanonical :
      coareaRoute ≡ Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary

    gradientBoundaryRecorded :
      Gradient.A4GradientFormulaLocalChartBoundaryRecorded ≡ true
    phiBoundaryRecorded :
      PhiJacobian.NSPhiJacobianLowerBoundBoundaryRecorded ≡ true
    coareaBoundaryRecorded :
      Coarea.NSA4CoareaStripPreimageCalculationBoundaryRecorded ≡ true

    gradientDerivativeStillFalse :
      Gradient.normalizeSumTangentDerivativeProved ≡ false
    gradientScalarFormulaStillFalse :
      Gradient.scalarGradientFormulaProved ≡ false
    gradientRankStillFalse :
      Gradient.rankNoncriticalConditionProved ≡ false
    gradientRouteStillFalse :
      Gradient.localChartRouteToCoareaStripEstimateProved ≡ false

    phiDerivativeComputationStillFalse :
      PhiJacobian.PhiChartDerivativeComputed ≡ false
    phiJacobianLowerBoundStillFalse :
      PhiJacobian.PhiQuantitativeJacobianLowerBoundProved ≡ false
    phiTheoremStillFalse :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ false

    coareaExactGradientStillFalse :
      Coarea.exactGradientFormulaProved ≡ false
    coareaTangentialJacobianStillFalse :
      Coarea.tangentialJacobianLowerBoundProved ≡ false
    coareaSlabStillFalse :
      Coarea.coareaSlabMeasureEstimateProved ≡ false
    coareaTheoremStillFalse :
      Coarea.analyticA4CoareaStripPreimageTheoremProved ≡ false

canonicalImportedDerivativeJacobianLowerBoundCompositeSupport :
  ImportedDerivativeJacobianLowerBoundCompositeSupport
canonicalImportedDerivativeJacobianLowerBoundCompositeSupport =
  record
    { gradientBoundary =
        Gradient.canonicalNSA4GradientFormulaLocalChartBoundary
    ; gradientBoundaryIsCanonical =
        refl
    ; phiJacobianBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; phiJacobianBoundaryIsCanonical =
        refl
    ; coareaBoundary =
        Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary
    ; coareaBoundaryIsCanonical =
        refl
    ; gradientImportedSupport =
        Gradient.canonicalImportedA4GradientFormulaLocalChartSupport
    ; gradientImportedSupportIsCanonical =
        refl
    ; gradientTarget =
        Gradient.canonicalA4GradientFormulaLocalChartTarget
    ; gradientTargetIsCanonical =
        refl
    ; localChartRoute =
        Gradient.canonicalLocalChartGradientToCoareaRoute
    ; localChartRouteIsCanonical =
        refl
    ; phiDerivativeFormula =
        PhiJacobian.canonicalPhiDerivativeFormulaCarrier
    ; phiDerivativeFormulaIsCanonical =
        refl
    ; phiRankCarrier =
        PhiJacobian.canonicalPhiChartRankCarrier
    ; phiRankCarrierIsCanonical =
        refl
    ; phiJacobianLowerBound =
        PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    ; phiJacobianLowerBoundIsCanonical =
        refl
    ; phiDegenerateTriadExclusion =
        PhiJacobian.canonicalDegenerateTriadExclusionCarrier
    ; phiDegenerateTriadExclusionIsCanonical =
        refl
    ; phiBudgetAbsorption =
        PhiJacobian.canonicalDegenerateTriadBudgetAbsorptionCarrier
    ; phiBudgetAbsorptionIsCanonical =
        refl
    ; phiCapUniformConstant =
        PhiJacobian.canonicalWhitneyCapUniformConstantCarrier
    ; phiCapUniformConstantIsCanonical =
        refl
    ; phiTarget =
        PhiJacobian.canonicalPhiJacobianLowerBoundTarget
    ; phiTargetIsCanonical =
        refl
    ; coareaExactGradient =
        Coarea.canonicalExactGradientFormulaCarrier
    ; coareaExactGradientIsCanonical =
        refl
    ; coareaTangentialJacobian =
        Coarea.canonicalTangentialJacobianLowerBoundCarrier
    ; coareaTangentialJacobianIsCanonical =
        refl
    ; coareaEtaStripSlab =
        Coarea.canonicalEtaStripSlabCarrier
    ; coareaEtaStripSlabIsCanonical =
        refl
    ; coareaLevelSetMeasure =
        Coarea.canonicalCoareaLevelSetMeasureCarrier
    ; coareaLevelSetMeasureIsCanonical =
        refl
    ; coareaSlabEstimate =
        Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    ; coareaSlabEstimateIsCanonical =
        refl
    ; coareaRoute =
        Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary
    ; coareaRouteIsCanonical =
        refl
    ; gradientBoundaryRecorded =
        refl
    ; phiBoundaryRecorded =
        refl
    ; coareaBoundaryRecorded =
        refl
    ; gradientDerivativeStillFalse =
        refl
    ; gradientScalarFormulaStillFalse =
        refl
    ; gradientRankStillFalse =
        refl
    ; gradientRouteStillFalse =
        refl
    ; phiDerivativeComputationStillFalse =
        refl
    ; phiJacobianLowerBoundStillFalse =
        refl
    ; phiTheoremStillFalse =
        refl
    ; coareaExactGradientStillFalse =
        refl
    ; coareaTangentialJacobianStillFalse =
        refl
    ; coareaSlabStillFalse =
        refl
    ; coareaTheoremStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Composite derivative-to-Jacobian route carriers.

data NormalizeSumDerivativeFormulaRouteCarrier : Set where
  localChartDerivativeFormulaAgreesWithPhiDerivativeCarrier :
    Gradient.NormalizeSumTangentDerivativeCarrier →
    Gradient.ScalarTangentGradientFormulaCarrier →
    PhiJacobian.PhiDerivativeFormulaCarrier →
    Coarea.ExactGradientFormulaCarrier →
    NormalizeSumDerivativeFormulaRouteCarrier

data ScalarGradientRankRouteCarrier : Set where
  scalarGradientFormulaFeedsRankNoncriticalPhiChartRank :
    NormalizeSumDerivativeFormulaRouteCarrier →
    Gradient.RankNoncriticalConditionCarrier →
    PhiJacobian.PhiChartRankCarrier →
    ScalarGradientRankRouteCarrier

data JacobianLowerBoundRouteCarrier : Set where
  phiRankAndDerivativeYieldTangentialCoareaJacobianLowerBound :
    ScalarGradientRankRouteCarrier →
    PhiJacobian.PhiJacobianLowerBoundCarrier →
    PhiJacobian.DegenerateTriadExclusionCarrier →
    PhiJacobian.DegenerateTriadBudgetAbsorptionCarrier →
    Coarea.TangentialJacobianLowerBoundCarrier →
    JacobianLowerBoundRouteCarrier

data UniformPacketConstantRouteCarrier : Set where
  lowerBoundConstantsTransportThroughWhitneyChartsToCoarea :
    JacobianLowerBoundRouteCarrier →
    Gradient.UniformChartCompatibilityCarrier →
    PhiJacobian.WhitneyCapUniformConstantCarrier →
    Coarea.UniformInNormalConstantCarrier →
    UniformPacketConstantRouteCarrier

data EtaStripCoareaLowerBoundRouteCarrier : Set where
  etaStripCoareaSlabUsesDerivativeJacobianAndUniformConstants :
    UniformPacketConstantRouteCarrier →
    Coarea.EtaStripSlabCarrier →
    Coarea.CoareaLevelSetMeasureCarrier →
    Coarea.EtaStripCoareaSlabEstimateCarrier →
    Coarea.CoareaRouteToOutputStripPreimageBoundary →
    EtaStripCoareaLowerBoundRouteCarrier

data DerivativeJacobianLowerBoundCompositeTarget : Set where
  derivativeFormulaAndPhiJacobianLowerBoundRouteRecorded :
    ImportedDerivativeJacobianLowerBoundCompositeSupport →
    NormalizeSumDerivativeFormulaRouteCarrier →
    ScalarGradientRankRouteCarrier →
    JacobianLowerBoundRouteCarrier →
    UniformPacketConstantRouteCarrier →
    EtaStripCoareaLowerBoundRouteCarrier →
    Gradient.A4GradientFormulaLocalChartTarget →
    PhiJacobian.PhiJacobianLowerBoundTarget →
    Coarea.A4CoareaStripPreimageCalculationTarget →
    DerivativeJacobianLowerBoundCompositeTarget

canonicalNormalizeSumDerivativeFormulaRouteCarrier :
  NormalizeSumDerivativeFormulaRouteCarrier
canonicalNormalizeSumDerivativeFormulaRouteCarrier =
  localChartDerivativeFormulaAgreesWithPhiDerivativeCarrier
    Gradient.canonicalNormalizeSumTangentDerivativeCarrier
    Gradient.canonicalScalarTangentGradientFormulaCarrier
    PhiJacobian.canonicalPhiDerivativeFormulaCarrier
    Coarea.canonicalExactGradientFormulaCarrier

canonicalScalarGradientRankRouteCarrier :
  ScalarGradientRankRouteCarrier
canonicalScalarGradientRankRouteCarrier =
  scalarGradientFormulaFeedsRankNoncriticalPhiChartRank
    canonicalNormalizeSumDerivativeFormulaRouteCarrier
    Gradient.canonicalRankNoncriticalConditionCarrier
    PhiJacobian.canonicalPhiChartRankCarrier

canonicalJacobianLowerBoundRouteCarrier :
  JacobianLowerBoundRouteCarrier
canonicalJacobianLowerBoundRouteCarrier =
  phiRankAndDerivativeYieldTangentialCoareaJacobianLowerBound
    canonicalScalarGradientRankRouteCarrier
    PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    PhiJacobian.canonicalDegenerateTriadExclusionCarrier
    PhiJacobian.canonicalDegenerateTriadBudgetAbsorptionCarrier
    Coarea.canonicalTangentialJacobianLowerBoundCarrier

canonicalUniformPacketConstantRouteCarrier :
  UniformPacketConstantRouteCarrier
canonicalUniformPacketConstantRouteCarrier =
  lowerBoundConstantsTransportThroughWhitneyChartsToCoarea
    canonicalJacobianLowerBoundRouteCarrier
    Gradient.canonicalUniformChartCompatibilityCarrier
    PhiJacobian.canonicalWhitneyCapUniformConstantCarrier
    Coarea.canonicalUniformInNormalConstantCarrier

canonicalEtaStripCoareaLowerBoundRouteCarrier :
  EtaStripCoareaLowerBoundRouteCarrier
canonicalEtaStripCoareaLowerBoundRouteCarrier =
  etaStripCoareaSlabUsesDerivativeJacobianAndUniformConstants
    canonicalUniformPacketConstantRouteCarrier
    Coarea.canonicalEtaStripSlabCarrier
    Coarea.canonicalCoareaLevelSetMeasureCarrier
    Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary

canonicalDerivativeJacobianLowerBoundCompositeTarget :
  DerivativeJacobianLowerBoundCompositeTarget
canonicalDerivativeJacobianLowerBoundCompositeTarget =
  derivativeFormulaAndPhiJacobianLowerBoundRouteRecorded
    canonicalImportedDerivativeJacobianLowerBoundCompositeSupport
    canonicalNormalizeSumDerivativeFormulaRouteCarrier
    canonicalScalarGradientRankRouteCarrier
    canonicalJacobianLowerBoundRouteCarrier
    canonicalUniformPacketConstantRouteCarrier
    canonicalEtaStripCoareaLowerBoundRouteCarrier
    Gradient.canonicalA4GradientFormulaLocalChartTarget
    PhiJacobian.canonicalPhiJacobianLowerBoundTarget
    Coarea.canonicalA4CoareaStripPreimageCalculationTarget

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data DerivativeJacobianLowerBoundCompositeObligation : Set where
  importAssignedGradientPhiJacobianAndCoareaBoundaries :
    DerivativeJacobianLowerBoundCompositeObligation
  identifyNormalizeSumDerivativeFormulaWithPhiDerivativeCarrier :
    DerivativeJacobianLowerBoundCompositeObligation
  projectDerivativeAgainstOutputNormalForScalarGradient :
    DerivativeJacobianLowerBoundCompositeObligation
  useScalarGradientForRankNoncriticalCondition :
    DerivativeJacobianLowerBoundCompositeObligation
  routePhiChartRankToQuantitativeJacobianLowerBound :
    DerivativeJacobianLowerBoundCompositeObligation
  excludeAntipodalNullAndRankDropDegenerateTriads :
    DerivativeJacobianLowerBoundCompositeObligation
  absorbDegenerateTriadsIntoLowerOrderA4Budget :
    DerivativeJacobianLowerBoundCompositeObligation
  keepWhitneyPacketConstantsUniformOnChartOverlaps :
    DerivativeJacobianLowerBoundCompositeObligation
  feedJacobianLowerBoundIntoTangentialCoareaJacobian :
    DerivativeJacobianLowerBoundCompositeObligation
  feedTangentialCoareaJacobianIntoEtaStripSlabEstimate :
    DerivativeJacobianLowerBoundCompositeObligation
  routeEtaStripEstimateToOutputPreimageConsumer :
    DerivativeJacobianLowerBoundCompositeObligation
  keepA4A6NSClayAndTerminalPromotionFalse :
    DerivativeJacobianLowerBoundCompositeObligation

canonicalDerivativeJacobianLowerBoundCompositeObligations :
  List DerivativeJacobianLowerBoundCompositeObligation
canonicalDerivativeJacobianLowerBoundCompositeObligations =
  importAssignedGradientPhiJacobianAndCoareaBoundaries
  ∷ identifyNormalizeSumDerivativeFormulaWithPhiDerivativeCarrier
  ∷ projectDerivativeAgainstOutputNormalForScalarGradient
  ∷ useScalarGradientForRankNoncriticalCondition
  ∷ routePhiChartRankToQuantitativeJacobianLowerBound
  ∷ excludeAntipodalNullAndRankDropDegenerateTriads
  ∷ absorbDegenerateTriadsIntoLowerOrderA4Budget
  ∷ keepWhitneyPacketConstantsUniformOnChartOverlaps
  ∷ feedJacobianLowerBoundIntoTangentialCoareaJacobian
  ∷ feedTangentialCoareaJacobianIntoEtaStripSlabEstimate
  ∷ routeEtaStripEstimateToOutputPreimageConsumer
  ∷ keepA4A6NSClayAndTerminalPromotionFalse
  ∷ []

DerivativeJacobianLowerBoundCompositeObligationCount : Nat
DerivativeJacobianLowerBoundCompositeObligationCount =
  listLength canonicalDerivativeJacobianLowerBoundCompositeObligations

DerivativeJacobianLowerBoundCompositeObligationCountIs12 :
  DerivativeJacobianLowerBoundCompositeObligationCount ≡ 12
DerivativeJacobianLowerBoundCompositeObligationCountIs12 =
  refl

data DerivativeJacobianLowerBoundCompositeBlocker : Set where
  gradientFormulaChildStillBoundaryOnly :
    DerivativeJacobianLowerBoundCompositeBlocker
  phiJacobianQuantitativeLowerBoundStillBoundaryOnly :
    DerivativeJacobianLowerBoundCompositeBlocker
  coareaStripPreimageCalculationStillBoundaryOnly :
    DerivativeJacobianLowerBoundCompositeBlocker
  missingConstructiveDerivativeFormulaProof :
    DerivativeJacobianLowerBoundCompositeBlocker
  missingRankNoncriticalAndRegularValueProof :
    DerivativeJacobianLowerBoundCompositeBlocker
  missingUniformWhitneyPacketConstantProof :
    DerivativeJacobianLowerBoundCompositeBlocker
  missingDegenerateTriadBudgetAbsorptionProof :
    DerivativeJacobianLowerBoundCompositeBlocker
  missingEtaStripCoareaSlabMeasureProof :
    DerivativeJacobianLowerBoundCompositeBlocker
  downstreamA4A6AndClayPromotionStillBlocked :
    DerivativeJacobianLowerBoundCompositeBlocker

canonicalDerivativeJacobianLowerBoundCompositeBlockers :
  List DerivativeJacobianLowerBoundCompositeBlocker
canonicalDerivativeJacobianLowerBoundCompositeBlockers =
  gradientFormulaChildStillBoundaryOnly
  ∷ phiJacobianQuantitativeLowerBoundStillBoundaryOnly
  ∷ coareaStripPreimageCalculationStillBoundaryOnly
  ∷ missingConstructiveDerivativeFormulaProof
  ∷ missingRankNoncriticalAndRegularValueProof
  ∷ missingUniformWhitneyPacketConstantProof
  ∷ missingDegenerateTriadBudgetAbsorptionProof
  ∷ missingEtaStripCoareaSlabMeasureProof
  ∷ downstreamA4A6AndClayPromotionStillBlocked
  ∷ []

DerivativeJacobianLowerBoundCompositeBlockerCount : Nat
DerivativeJacobianLowerBoundCompositeBlockerCount =
  listLength canonicalDerivativeJacobianLowerBoundCompositeBlockers

DerivativeJacobianLowerBoundCompositeBlockerCountIs9 :
  DerivativeJacobianLowerBoundCompositeBlockerCount ≡ 9
DerivativeJacobianLowerBoundCompositeBlockerCountIs9 =
  refl

data DerivativeJacobianLowerBoundCompositeStatusRow : Set where
  assignedChildBoundariesImportedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  localDerivativeFormulaRouteRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  scalarGradientRankRouteRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  phiJacobianLowerBoundRouteRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  degenerateTriadBudgetRouteRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  uniformPacketConstantRouteRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  etaStripCoareaLowerBoundRouteRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  obligationsAndBlockersRecordedStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow
  allProofAndPromotionFlagsFalseStatus :
    DerivativeJacobianLowerBoundCompositeStatusRow

canonicalDerivativeJacobianLowerBoundCompositeStatusRows :
  List DerivativeJacobianLowerBoundCompositeStatusRow
canonicalDerivativeJacobianLowerBoundCompositeStatusRows =
  assignedChildBoundariesImportedStatus
  ∷ localDerivativeFormulaRouteRecordedStatus
  ∷ scalarGradientRankRouteRecordedStatus
  ∷ phiJacobianLowerBoundRouteRecordedStatus
  ∷ degenerateTriadBudgetRouteRecordedStatus
  ∷ uniformPacketConstantRouteRecordedStatus
  ∷ etaStripCoareaLowerBoundRouteRecordedStatus
  ∷ obligationsAndBlockersRecordedStatus
  ∷ allProofAndPromotionFlagsFalseStatus
  ∷ []

DerivativeJacobianLowerBoundCompositeStatusRowCount : Nat
DerivativeJacobianLowerBoundCompositeStatusRowCount =
  listLength canonicalDerivativeJacobianLowerBoundCompositeStatusRows

DerivativeJacobianLowerBoundCompositeStatusRowCountIs9 :
  DerivativeJacobianLowerBoundCompositeStatusRowCount ≡ 9
DerivativeJacobianLowerBoundCompositeStatusRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Fail-closed flags and promotion guards.

data DerivativeJacobianLowerBoundCompositePromotion : Set where

DerivativeJacobianLowerBoundCompositePromotionImpossibleHere :
  DerivativeJacobianLowerBoundCompositePromotion →
  ⊥
DerivativeJacobianLowerBoundCompositePromotionImpossibleHere ()

NSA4DerivativeJacobianLowerBoundCompositeBoundaryRecorded : Bool
NSA4DerivativeJacobianLowerBoundCompositeBoundaryRecorded =
  true

derivativeFormulaRouteRecorded : Bool
derivativeFormulaRouteRecorded =
  true

scalarGradientRankRouteRecorded : Bool
scalarGradientRankRouteRecorded =
  true

jacobianLowerBoundRouteRecorded : Bool
jacobianLowerBoundRouteRecorded =
  true

etaStripCoareaRouteRecorded : Bool
etaStripCoareaRouteRecorded =
  true

derivativeFormulaRouteProved : Bool
derivativeFormulaRouteProved =
  false

scalarGradientRankRouteProved : Bool
scalarGradientRankRouteProved =
  false

jacobianLowerBoundRouteProved : Bool
jacobianLowerBoundRouteProved =
  false

etaStripCoareaRouteProved : Bool
etaStripCoareaRouteProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

A6TriadicCompensatedLeakageIdentityProved : Bool
A6TriadicCompensatedLeakageIdentityProved =
  false

fullLocalDefectMonotonicityProved : Bool
fullLocalDefectMonotonicityProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsDerivativeJacobianLowerBoundCompositeBoundary :
  NSA4DerivativeJacobianLowerBoundCompositeBoundaryRecorded ≡ true
recordsDerivativeJacobianLowerBoundCompositeBoundary =
  refl

recordsDerivativeFormulaRoute :
  derivativeFormulaRouteRecorded ≡ true
recordsDerivativeFormulaRoute =
  refl

recordsScalarGradientRankRoute :
  scalarGradientRankRouteRecorded ≡ true
recordsScalarGradientRankRoute =
  refl

recordsJacobianLowerBoundRoute :
  jacobianLowerBoundRouteRecorded ≡ true
recordsJacobianLowerBoundRoute =
  refl

recordsEtaStripCoareaRoute :
  etaStripCoareaRouteRecorded ≡ true
recordsEtaStripCoareaRoute =
  refl

keepsDerivativeFormulaRouteProvedFalse :
  derivativeFormulaRouteProved ≡ false
keepsDerivativeFormulaRouteProvedFalse =
  refl

keepsScalarGradientRankRouteProvedFalse :
  scalarGradientRankRouteProved ≡ false
keepsScalarGradientRankRouteProvedFalse =
  refl

keepsJacobianLowerBoundRouteProvedFalse :
  jacobianLowerBoundRouteProved ≡ false
keepsJacobianLowerBoundRouteProvedFalse =
  refl

keepsEtaStripCoareaRouteProvedFalse :
  etaStripCoareaRouteProved ≡ false
keepsEtaStripCoareaRouteProvedFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingProvedFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingProvedFalse =
  refl

keepsA6TriadicCompensatedLeakageIdentityProvedFalse :
  A6TriadicCompensatedLeakageIdentityProved ≡ false
keepsA6TriadicCompensatedLeakageIdentityProvedFalse =
  refl

keepsFullLocalDefectMonotonicityProvedFalse :
  fullLocalDefectMonotonicityProved ≡ false
keepsFullLocalDefectMonotonicityProvedFalse =
  refl

keepsClayNavierStokesPromotedFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotedFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

data DerivativeJacobianLowerBoundCompositeClaimState : Set where
  boundaryRecordedButAnalyticProofsStillFalse :
    DerivativeJacobianLowerBoundCompositeClaimState
  derivativeAndJacobianRouteComposedButNotPromoted :
    DerivativeJacobianLowerBoundCompositeClaimState
  coareaConsumerRecordedButA4A6ClayStillBlocked :
    DerivativeJacobianLowerBoundCompositeClaimState

canonicalDerivativeJacobianLowerBoundCompositeClaimStates :
  List DerivativeJacobianLowerBoundCompositeClaimState
canonicalDerivativeJacobianLowerBoundCompositeClaimStates =
  boundaryRecordedButAnalyticProofsStillFalse
  ∷ derivativeAndJacobianRouteComposedButNotPromoted
  ∷ coareaConsumerRecordedButA4A6ClayStillBlocked
  ∷ []

DerivativeJacobianLowerBoundCompositeClaimStateCount : Nat
DerivativeJacobianLowerBoundCompositeClaimStateCount =
  listLength canonicalDerivativeJacobianLowerBoundCompositeClaimStates

DerivativeJacobianLowerBoundCompositeClaimStateCountIs3 :
  DerivativeJacobianLowerBoundCompositeClaimStateCount ≡ 3
DerivativeJacobianLowerBoundCompositeClaimStateCountIs3 =
  refl

------------------------------------------------------------------------
-- Boundary receipt.

record DerivativeJacobianLowerBoundCompositeBoundaryReceipt : Set where
  field
    moduleName :
      String
    objective :
      String
    importedSupport :
      ImportedDerivativeJacobianLowerBoundCompositeSupport
    target :
      DerivativeJacobianLowerBoundCompositeTarget
    derivativeRoute :
      NormalizeSumDerivativeFormulaRouteCarrier
    rankRoute :
      ScalarGradientRankRouteCarrier
    jacobianRoute :
      JacobianLowerBoundRouteCarrier
    uniformRoute :
      UniformPacketConstantRouteCarrier
    etaStripRoute :
      EtaStripCoareaLowerBoundRouteCarrier
    obligations :
      List DerivativeJacobianLowerBoundCompositeObligation
    obligationCountIsCanonical :
      DerivativeJacobianLowerBoundCompositeObligationCount ≡ 12
    blockers :
      List DerivativeJacobianLowerBoundCompositeBlocker
    blockerCountIsCanonical :
      DerivativeJacobianLowerBoundCompositeBlockerCount ≡ 9
    statusRows :
      List DerivativeJacobianLowerBoundCompositeStatusRow
    statusRowCountIsCanonical :
      DerivativeJacobianLowerBoundCompositeStatusRowCount ≡ 9
    claimStates :
      List DerivativeJacobianLowerBoundCompositeClaimState
    claimStateCountIsCanonical :
      DerivativeJacobianLowerBoundCompositeClaimStateCount ≡ 3
    boundaryRecorded :
      NSA4DerivativeJacobianLowerBoundCompositeBoundaryRecorded ≡ true
    derivativeRouteRecorded :
      derivativeFormulaRouteRecorded ≡ true
    rankRouteRecorded :
      scalarGradientRankRouteRecorded ≡ true
    jacobianRouteRecorded :
      jacobianLowerBoundRouteRecorded ≡ true
    coareaRouteRecorded :
      etaStripCoareaRouteRecorded ≡ true
    derivativeRouteStillFalse :
      derivativeFormulaRouteProved ≡ false
    rankRouteStillFalse :
      scalarGradientRankRouteProved ≡ false
    jacobianRouteStillFalse :
      jacobianLowerBoundRouteProved ≡ false
    etaStripRouteStillFalse :
      etaStripCoareaRouteProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    localDefectMonotonicityStillFalse :
      fullLocalDefectMonotonicityProved ≡ false
    clayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false

canonicalDerivativeJacobianLowerBoundCompositeBoundaryReceipt :
  DerivativeJacobianLowerBoundCompositeBoundaryReceipt
canonicalDerivativeJacobianLowerBoundCompositeBoundaryReceipt =
  record
    { moduleName =
        "DASHI.Physics.Closure.NSA4DerivativeJacobianLowerBoundCompositeBoundary"
    ; objective =
        "Compose the A4 local-chart derivative formula, Phi-Jacobian lower-bound target, and coarea strip-preimage calculation into one fail-closed derivative-to-Jacobian route."
    ; importedSupport =
        canonicalImportedDerivativeJacobianLowerBoundCompositeSupport
    ; target =
        canonicalDerivativeJacobianLowerBoundCompositeTarget
    ; derivativeRoute =
        canonicalNormalizeSumDerivativeFormulaRouteCarrier
    ; rankRoute =
        canonicalScalarGradientRankRouteCarrier
    ; jacobianRoute =
        canonicalJacobianLowerBoundRouteCarrier
    ; uniformRoute =
        canonicalUniformPacketConstantRouteCarrier
    ; etaStripRoute =
        canonicalEtaStripCoareaLowerBoundRouteCarrier
    ; obligations =
        canonicalDerivativeJacobianLowerBoundCompositeObligations
    ; obligationCountIsCanonical =
        refl
    ; blockers =
        canonicalDerivativeJacobianLowerBoundCompositeBlockers
    ; blockerCountIsCanonical =
        refl
    ; statusRows =
        canonicalDerivativeJacobianLowerBoundCompositeStatusRows
    ; statusRowCountIsCanonical =
        refl
    ; claimStates =
        canonicalDerivativeJacobianLowerBoundCompositeClaimStates
    ; claimStateCountIsCanonical =
        refl
    ; boundaryRecorded =
        refl
    ; derivativeRouteRecorded =
        refl
    ; rankRouteRecorded =
        refl
    ; jacobianRouteRecorded =
        refl
    ; coareaRouteRecorded =
        refl
    ; derivativeRouteStillFalse =
        refl
    ; rankRouteStillFalse =
        refl
    ; jacobianRouteStillFalse =
        refl
    ; etaStripRouteStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; localDefectMonotonicityStillFalse =
        refl
    ; clayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    }

record NSA4DerivativeJacobianLowerBoundCompositeBoundary : Set where
  field
    receipt :
      DerivativeJacobianLowerBoundCompositeBoundaryReceipt
    importedSupport :
      ImportedDerivativeJacobianLowerBoundCompositeSupport
    target :
      DerivativeJacobianLowerBoundCompositeTarget
    derivativeRoute :
      NormalizeSumDerivativeFormulaRouteCarrier
    rankRoute :
      ScalarGradientRankRouteCarrier
    jacobianRoute :
      JacobianLowerBoundRouteCarrier
    etaStripRoute :
      EtaStripCoareaLowerBoundRouteCarrier
    gradientBoundary :
      Gradient.NSA4GradientFormulaLocalChartBoundary
    phiJacobianBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    coareaBoundary :
      Coarea.NSA4CoareaStripPreimageCalculationBoundary
    boundaryRecorded :
      NSA4DerivativeJacobianLowerBoundCompositeBoundaryRecorded ≡ true
    derivativeRouteStillFalse :
      derivativeFormulaRouteProved ≡ false
    scalarRankRouteStillFalse :
      scalarGradientRankRouteProved ≡ false
    jacobianRouteStillFalse :
      jacobianLowerBoundRouteProved ≡ false
    etaStripRouteStillFalse :
      etaStripCoareaRouteProved ≡ false
    childGradientDerivativeStillFalse :
      Gradient.normalizeSumTangentDerivativeProved ≡ false
    childPhiJacobianStillFalse :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ false
    childCoareaStillFalse :
      Coarea.analyticA4CoareaStripPreimageTheoremProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    clayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false
    contradiction :
      A4LeiRenTianFourierOutputCouplingProved ≡ true → ⊥

canonicalNSA4DerivativeJacobianLowerBoundCompositeBoundary :
  NSA4DerivativeJacobianLowerBoundCompositeBoundary
canonicalNSA4DerivativeJacobianLowerBoundCompositeBoundary =
  record
    { receipt =
        canonicalDerivativeJacobianLowerBoundCompositeBoundaryReceipt
    ; importedSupport =
        canonicalImportedDerivativeJacobianLowerBoundCompositeSupport
    ; target =
        canonicalDerivativeJacobianLowerBoundCompositeTarget
    ; derivativeRoute =
        canonicalNormalizeSumDerivativeFormulaRouteCarrier
    ; rankRoute =
        canonicalScalarGradientRankRouteCarrier
    ; jacobianRoute =
        canonicalJacobianLowerBoundRouteCarrier
    ; etaStripRoute =
        canonicalEtaStripCoareaLowerBoundRouteCarrier
    ; gradientBoundary =
        Gradient.canonicalNSA4GradientFormulaLocalChartBoundary
    ; phiJacobianBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; coareaBoundary =
        Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary
    ; boundaryRecorded =
        refl
    ; derivativeRouteStillFalse =
        refl
    ; scalarRankRouteStillFalse =
        refl
    ; jacobianRouteStillFalse =
        refl
    ; etaStripRouteStillFalse =
        refl
    ; childGradientDerivativeStillFalse =
        refl
    ; childPhiJacobianStillFalse =
        refl
    ; childCoareaStillFalse =
        refl
    ; A4StillFalse =
        refl
    ; A6StillFalse =
        refl
    ; clayStillFalse =
        refl
    ; terminalStillFalse =
        refl
    ; contradiction =
        λ ()
    }

open NSA4DerivativeJacobianLowerBoundCompositeBoundary public
