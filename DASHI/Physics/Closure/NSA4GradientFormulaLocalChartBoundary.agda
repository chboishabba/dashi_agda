module DASHI.Physics.Closure.NSA4GradientFormulaLocalChartBoundary where

-- Fail-closed boundary for the local-chart gradient formula behind the
-- A4 coarea strip calculation.
--
-- Scalar map:
--
--   f_n(theta1,theta2)
--     = < normalize(theta1 + theta2) , n >
--
-- on the non-antipodal product-angular domain.  The intended analytic
-- local-chart obligation records:
--
--   chart atlas on the non-antipodal domain
--     -> tangent derivative of normalize(theta1 + theta2)
--     -> scalar projection against n
--     -> rank/noncritical condition for regular output normals
--     -> uniform chart compatibility across Whitney packets
--     -> feed into NSA4CoareaStripPreimageCalculationBoundary.
--
-- This file records the theorem shape and routing only.  It proves no
-- local chart atlas theorem, no normalize-sum derivative theorem, no
-- rank/noncritical theorem, no coarea theorem, no A4 theorem, no A6
-- leakage theorem, no Navier-Stokes Clay result, and no terminal
-- promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSA4CoareaStripPreimageCalculationBoundary
  as Coarea
import DASHI.Physics.Closure.NSAntipodalTubeNullMassBoundary
  as Antipodal
import DASHI.Physics.Closure.NSFourierOutputPushforwardBoundary
  as Pushforward
import DASHI.Physics.Closure.NSPhiJacobianLowerBoundBoundary
  as PhiJacobian
import DASHI.Physics.Closure.NSSardRegularValueSlicingBoundary
  as Sard

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported child surfaces.

record ImportedA4GradientFormulaLocalChartSupport : Set where
  field
    coareaBoundary :
      Coarea.NSA4CoareaStripPreimageCalculationBoundary
    coareaBoundaryIsCanonical :
      coareaBoundary
        ≡ Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary

    phiJacobianBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    phiJacobianBoundaryIsCanonical :
      phiJacobianBoundary
        ≡ PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary

    sardSlicingBoundary :
      Sard.NSSardRegularValueSlicingBoundary
    sardSlicingBoundaryIsCanonical :
      sardSlicingBoundary
        ≡ Sard.canonicalNSSardRegularValueSlicingBoundary

    nonAntipodalDomain :
      Antipodal.NormalizeSumDomainExclusion
    nonAntipodalDomainIsCanonical :
      nonAntipodalDomain ≡ Antipodal.canonicalNormalizeSumDomainExclusion

    phiNormalizeSumMap :
      Pushforward.FourierOutputPhiMap
    phiNormalizeSumMapIsCanonical :
      phiNormalizeSumMap ≡ Pushforward.canonicalFourierOutputPhiMap

    sardChartAtlas :
      Sard.SmoothChartAtlasCarrier
    sardChartAtlasIsCanonical :
      sardChartAtlas ≡ Sard.canonicalSmoothChartAtlasCarrier

    sardPhiDifferential :
      Sard.PhiDifferentialCarrier
    sardPhiDifferentialIsCanonical :
      sardPhiDifferential ≡ Sard.canonicalPhiDifferentialCarrier

    sardRegularValue :
      Sard.RegularValueCarrier
    sardRegularValueIsCanonical :
      sardRegularValue ≡ Sard.canonicalRegularValueCarrier

    phiDerivativeFormula :
      PhiJacobian.PhiDerivativeFormulaCarrier
    phiDerivativeFormulaIsCanonical :
      phiDerivativeFormula ≡ PhiJacobian.canonicalPhiDerivativeFormulaCarrier

    phiChartRank :
      PhiJacobian.PhiChartRankCarrier
    phiChartRankIsCanonical :
      phiChartRank ≡ PhiJacobian.canonicalPhiChartRankCarrier

    phiJacobianLowerBound :
      PhiJacobian.PhiJacobianLowerBoundCarrier
    phiJacobianLowerBoundIsCanonical :
      phiJacobianLowerBound
        ≡ PhiJacobian.canonicalPhiJacobianLowerBoundCarrier

    coareaScalarFunction :
      Coarea.ScalarA4CoareaFunctionCarrier
    coareaScalarFunctionIsCanonical :
      coareaScalarFunction ≡ Coarea.canonicalScalarA4CoareaFunctionCarrier

    coareaGradientFormula :
      Coarea.ExactGradientFormulaCarrier
    coareaGradientFormulaIsCanonical :
      coareaGradientFormula ≡ Coarea.canonicalExactGradientFormulaCarrier

    coareaRoute :
      Coarea.CoareaRouteToOutputStripPreimageBoundary
    coareaRouteIsCanonical :
      coareaRoute ≡ Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary

    sardChartAtlasStillFalse :
      Sard.smoothChartAtlasConstructed ≡ false
    sardDerivativeRankStillFalse :
      Sard.derivativeRankProofCompleted ≡ false
    sardRegularValueStillFalse :
      Sard.SardRegularValueSlicingProved ≡ false
    phiDerivativeComputationStillFalse :
      PhiJacobian.PhiChartDerivativeComputed ≡ false
    phiQuantitativeJacobianStillFalse :
      PhiJacobian.PhiQuantitativeJacobianLowerBoundProved ≡ false
    phiJacobianTheoremStillFalse :
      PhiJacobian.PhiJacobianLowerBoundTheoremProved ≡ false
    coareaExactGradientStillFalse :
      Coarea.exactGradientFormulaProved ≡ false
    coareaTangentialJacobianStillFalse :
      Coarea.tangentialJacobianLowerBoundProved ≡ false
    coareaSlabMeasureStillFalse :
      Coarea.coareaSlabMeasureEstimateProved ≡ false
    coareaTheoremStillFalse :
      Coarea.analyticA4CoareaStripPreimageTheoremProved ≡ false

canonicalImportedA4GradientFormulaLocalChartSupport :
  ImportedA4GradientFormulaLocalChartSupport
canonicalImportedA4GradientFormulaLocalChartSupport =
  record
    { coareaBoundary =
        Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary
    ; coareaBoundaryIsCanonical =
        refl
    ; phiJacobianBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; phiJacobianBoundaryIsCanonical =
        refl
    ; sardSlicingBoundary =
        Sard.canonicalNSSardRegularValueSlicingBoundary
    ; sardSlicingBoundaryIsCanonical =
        refl
    ; nonAntipodalDomain =
        Antipodal.canonicalNormalizeSumDomainExclusion
    ; nonAntipodalDomainIsCanonical =
        refl
    ; phiNormalizeSumMap =
        Pushforward.canonicalFourierOutputPhiMap
    ; phiNormalizeSumMapIsCanonical =
        refl
    ; sardChartAtlas =
        Sard.canonicalSmoothChartAtlasCarrier
    ; sardChartAtlasIsCanonical =
        refl
    ; sardPhiDifferential =
        Sard.canonicalPhiDifferentialCarrier
    ; sardPhiDifferentialIsCanonical =
        refl
    ; sardRegularValue =
        Sard.canonicalRegularValueCarrier
    ; sardRegularValueIsCanonical =
        refl
    ; phiDerivativeFormula =
        PhiJacobian.canonicalPhiDerivativeFormulaCarrier
    ; phiDerivativeFormulaIsCanonical =
        refl
    ; phiChartRank =
        PhiJacobian.canonicalPhiChartRankCarrier
    ; phiChartRankIsCanonical =
        refl
    ; phiJacobianLowerBound =
        PhiJacobian.canonicalPhiJacobianLowerBoundCarrier
    ; phiJacobianLowerBoundIsCanonical =
        refl
    ; coareaScalarFunction =
        Coarea.canonicalScalarA4CoareaFunctionCarrier
    ; coareaScalarFunctionIsCanonical =
        refl
    ; coareaGradientFormula =
        Coarea.canonicalExactGradientFormulaCarrier
    ; coareaGradientFormulaIsCanonical =
        refl
    ; coareaRoute =
        Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary
    ; coareaRouteIsCanonical =
        refl
    ; sardChartAtlasStillFalse =
        refl
    ; sardDerivativeRankStillFalse =
        refl
    ; sardRegularValueStillFalse =
        refl
    ; phiDerivativeComputationStillFalse =
        refl
    ; phiQuantitativeJacobianStillFalse =
        refl
    ; phiJacobianTheoremStillFalse =
        refl
    ; coareaExactGradientStillFalse =
        refl
    ; coareaTangentialJacobianStillFalse =
        refl
    ; coareaSlabMeasureStillFalse =
        refl
    ; coareaTheoremStillFalse =
        refl
    }

------------------------------------------------------------------------
-- Local-chart gradient formula carriers.

data LocalChartCoordinatePatchCarrier : Set where
  productSphericalChartPatchAvoidingAntipodalSumZero :
    Sard.SmoothChartAtlasCarrier →
    Antipodal.NormalizeSumDomainExclusion →
    LocalChartCoordinatePatchCarrier

data LocalChartAtlasCompatibilityCarrier : Set where
  finiteSmoothAtlasCoversNonAntipodalPairDomainWithSmoothTransitions :
    LocalChartCoordinatePatchCarrier →
    Sard.SmoothChartAtlasCarrier →
    LocalChartAtlasCompatibilityCarrier

data TangentPairCarrier : Set where
  tangentVectorsToThetaOneThetaTwoWithinChart :
    LocalChartCoordinatePatchCarrier →
    Pushforward.InputAngularPairCarrier →
    TangentPairCarrier

data NormalizeSumLocalExpressionCarrier : Set where
  localExpressionThetaSumDividedByPositiveNorm :
    Pushforward.FourierOutputPhiMap →
    LocalChartAtlasCompatibilityCarrier →
    TangentPairCarrier →
    NormalizeSumLocalExpressionCarrier

data NormalizeSumTangentDerivativeCarrier : Set where
  derivativeIsOrthogonalProjectionOfTangentSumOverThetaSumNorm :
    NormalizeSumLocalExpressionCarrier →
    PhiJacobian.PhiDerivativeFormulaCarrier →
    NormalizeSumTangentDerivativeCarrier

data OutputNormalLocalChartCarrier : Set where
  fixedUnitNormalNForGreatCircleOutputSlice :
    Coarea.OutputNormalCarrier →
    Sard.RegularValueCarrier →
    OutputNormalLocalChartCarrier

data ScalarLocalChartFunctionCarrier : Set where
  fNEqualsInnerProductOfNormalizeSumWithOutputNormal :
    NormalizeSumLocalExpressionCarrier →
    OutputNormalLocalChartCarrier →
    Coarea.ScalarA4CoareaFunctionCarrier →
    ScalarLocalChartFunctionCarrier

data ScalarTangentGradientFormulaCarrier : Set where
  gradientOfFNIsNormalProjectionComposedWithNormalizeSumDerivative :
    ScalarLocalChartFunctionCarrier →
    NormalizeSumTangentDerivativeCarrier →
    Coarea.ExactGradientFormulaCarrier →
    ScalarTangentGradientFormulaCarrier

data RankNoncriticalConditionCarrier : Set where
  noncriticalWhenOutputNormalAvoidsCriticalValuesAndRankDropLocus :
    ScalarTangentGradientFormulaCarrier →
    Sard.CriticalSetAwayFromAntipodalCarrier →
    Sard.SardExceptionalSetCarrier →
    PhiJacobian.PhiChartRankCarrier →
    PhiJacobian.PhiJacobianLowerBoundCarrier →
    RankNoncriticalConditionCarrier

data UniformChartCompatibilityCarrier : Set where
  gradientsAndJacobianBoundsAgreeOnChartOverlapsUniformly :
    LocalChartAtlasCompatibilityCarrier →
    RankNoncriticalConditionCarrier →
    PhiJacobian.WhitneyCapUniformConstantCarrier →
    PhiJacobian.OutputStripWidthRelationCarrier →
    UniformChartCompatibilityCarrier

data LocalChartGradientToCoareaRoute : Set where
  localGradientRankAndUniformChartsFeedCoareaStripCalculation :
    ScalarTangentGradientFormulaCarrier →
    RankNoncriticalConditionCarrier →
    UniformChartCompatibilityCarrier →
    Coarea.TangentialJacobianLowerBoundCarrier →
    Coarea.EtaStripCoareaSlabEstimateCarrier →
    Coarea.CoareaRouteToOutputStripPreimageBoundary →
    Coarea.NSA4CoareaStripPreimageCalculationBoundary →
    LocalChartGradientToCoareaRoute

data A4GradientFormulaLocalChartTarget : Set where
  localChartGradientFormulaForNormalizeSumDotNormalRecorded :
    ImportedA4GradientFormulaLocalChartSupport →
    LocalChartCoordinatePatchCarrier →
    LocalChartAtlasCompatibilityCarrier →
    TangentPairCarrier →
    NormalizeSumLocalExpressionCarrier →
    NormalizeSumTangentDerivativeCarrier →
    OutputNormalLocalChartCarrier →
    ScalarLocalChartFunctionCarrier →
    ScalarTangentGradientFormulaCarrier →
    RankNoncriticalConditionCarrier →
    UniformChartCompatibilityCarrier →
    LocalChartGradientToCoareaRoute →
    A4GradientFormulaLocalChartTarget

canonicalLocalChartCoordinatePatchCarrier :
  LocalChartCoordinatePatchCarrier
canonicalLocalChartCoordinatePatchCarrier =
  productSphericalChartPatchAvoidingAntipodalSumZero
    Sard.canonicalSmoothChartAtlasCarrier
    Antipodal.canonicalNormalizeSumDomainExclusion

canonicalLocalChartAtlasCompatibilityCarrier :
  LocalChartAtlasCompatibilityCarrier
canonicalLocalChartAtlasCompatibilityCarrier =
  finiteSmoothAtlasCoversNonAntipodalPairDomainWithSmoothTransitions
    canonicalLocalChartCoordinatePatchCarrier
    Sard.canonicalSmoothChartAtlasCarrier

canonicalTangentPairCarrier :
  TangentPairCarrier
canonicalTangentPairCarrier =
  tangentVectorsToThetaOneThetaTwoWithinChart
    canonicalLocalChartCoordinatePatchCarrier
    Pushforward.canonicalInputAngularPairCarrier

canonicalNormalizeSumLocalExpressionCarrier :
  NormalizeSumLocalExpressionCarrier
canonicalNormalizeSumLocalExpressionCarrier =
  localExpressionThetaSumDividedByPositiveNorm
    Pushforward.canonicalFourierOutputPhiMap
    canonicalLocalChartAtlasCompatibilityCarrier
    canonicalTangentPairCarrier

canonicalNormalizeSumTangentDerivativeCarrier :
  NormalizeSumTangentDerivativeCarrier
canonicalNormalizeSumTangentDerivativeCarrier =
  derivativeIsOrthogonalProjectionOfTangentSumOverThetaSumNorm
    canonicalNormalizeSumLocalExpressionCarrier
    PhiJacobian.canonicalPhiDerivativeFormulaCarrier

canonicalOutputNormalLocalChartCarrier :
  OutputNormalLocalChartCarrier
canonicalOutputNormalLocalChartCarrier =
  fixedUnitNormalNForGreatCircleOutputSlice
    Coarea.canonicalOutputNormalCarrier
    Sard.canonicalRegularValueCarrier

canonicalScalarLocalChartFunctionCarrier :
  ScalarLocalChartFunctionCarrier
canonicalScalarLocalChartFunctionCarrier =
  fNEqualsInnerProductOfNormalizeSumWithOutputNormal
    canonicalNormalizeSumLocalExpressionCarrier
    canonicalOutputNormalLocalChartCarrier
    Coarea.canonicalScalarA4CoareaFunctionCarrier

canonicalScalarTangentGradientFormulaCarrier :
  ScalarTangentGradientFormulaCarrier
canonicalScalarTangentGradientFormulaCarrier =
  gradientOfFNIsNormalProjectionComposedWithNormalizeSumDerivative
    canonicalScalarLocalChartFunctionCarrier
    canonicalNormalizeSumTangentDerivativeCarrier
    Coarea.canonicalExactGradientFormulaCarrier

canonicalRankNoncriticalConditionCarrier :
  RankNoncriticalConditionCarrier
canonicalRankNoncriticalConditionCarrier =
  noncriticalWhenOutputNormalAvoidsCriticalValuesAndRankDropLocus
    canonicalScalarTangentGradientFormulaCarrier
    Sard.canonicalCriticalSetAwayFromAntipodalCarrier
    Sard.canonicalSardExceptionalSetCarrier
    PhiJacobian.canonicalPhiChartRankCarrier
    PhiJacobian.canonicalPhiJacobianLowerBoundCarrier

canonicalUniformChartCompatibilityCarrier :
  UniformChartCompatibilityCarrier
canonicalUniformChartCompatibilityCarrier =
  gradientsAndJacobianBoundsAgreeOnChartOverlapsUniformly
    canonicalLocalChartAtlasCompatibilityCarrier
    canonicalRankNoncriticalConditionCarrier
    PhiJacobian.canonicalWhitneyCapUniformConstantCarrier
    PhiJacobian.canonicalOutputStripWidthRelationCarrier

canonicalLocalChartGradientToCoareaRoute :
  LocalChartGradientToCoareaRoute
canonicalLocalChartGradientToCoareaRoute =
  localGradientRankAndUniformChartsFeedCoareaStripCalculation
    canonicalScalarTangentGradientFormulaCarrier
    canonicalRankNoncriticalConditionCarrier
    canonicalUniformChartCompatibilityCarrier
    Coarea.canonicalTangentialJacobianLowerBoundCarrier
    Coarea.canonicalEtaStripCoareaSlabEstimateCarrier
    Coarea.canonicalCoareaRouteToOutputStripPreimageBoundary
    Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary

canonicalA4GradientFormulaLocalChartTarget :
  A4GradientFormulaLocalChartTarget
canonicalA4GradientFormulaLocalChartTarget =
  localChartGradientFormulaForNormalizeSumDotNormalRecorded
    canonicalImportedA4GradientFormulaLocalChartSupport
    canonicalLocalChartCoordinatePatchCarrier
    canonicalLocalChartAtlasCompatibilityCarrier
    canonicalTangentPairCarrier
    canonicalNormalizeSumLocalExpressionCarrier
    canonicalNormalizeSumTangentDerivativeCarrier
    canonicalOutputNormalLocalChartCarrier
    canonicalScalarLocalChartFunctionCarrier
    canonicalScalarTangentGradientFormulaCarrier
    canonicalRankNoncriticalConditionCarrier
    canonicalUniformChartCompatibilityCarrier
    canonicalLocalChartGradientToCoareaRoute

------------------------------------------------------------------------
-- Obligations, blockers, and status rows.

data A4GradientFormulaLocalChartObligation : Set where
  importCoareaPhiJacobianAndSardBoundarySurfaces :
    A4GradientFormulaLocalChartObligation
  fixNonAntipodalDomainForNormalizeSum :
    A4GradientFormulaLocalChartObligation
  buildSmoothLocalChartAtlasOnAngularPairDomain :
    A4GradientFormulaLocalChartObligation
  proveChartTransitionCompatibilityOnOverlaps :
    A4GradientFormulaLocalChartObligation
  writeNormalizeSumAsThetaSumOverPositiveNormInCharts :
    A4GradientFormulaLocalChartObligation
  computeTangentDerivativeOfNormalizeSum :
    A4GradientFormulaLocalChartObligation
  projectDerivativeAgainstFixedOutputNormalN :
    A4GradientFormulaLocalChartObligation
  recordScalarGradientFormulaForFN :
    A4GradientFormulaLocalChartObligation
  proveRankNoncriticalConditionAwayFromSardExceptionalValues :
    A4GradientFormulaLocalChartObligation
  keepJacobianLowerBoundUniformAcrossWhitneyChartPackets :
    A4GradientFormulaLocalChartObligation
  transportLocalGradientDataIntoCoareaStripEstimate :
    A4GradientFormulaLocalChartObligation
  keepProofA4A6NSClayAndTerminalPromotionFalse :
    A4GradientFormulaLocalChartObligation

canonicalA4GradientFormulaLocalChartObligations :
  List A4GradientFormulaLocalChartObligation
canonicalA4GradientFormulaLocalChartObligations =
  importCoareaPhiJacobianAndSardBoundarySurfaces
  ∷ fixNonAntipodalDomainForNormalizeSum
  ∷ buildSmoothLocalChartAtlasOnAngularPairDomain
  ∷ proveChartTransitionCompatibilityOnOverlaps
  ∷ writeNormalizeSumAsThetaSumOverPositiveNormInCharts
  ∷ computeTangentDerivativeOfNormalizeSum
  ∷ projectDerivativeAgainstFixedOutputNormalN
  ∷ recordScalarGradientFormulaForFN
  ∷ proveRankNoncriticalConditionAwayFromSardExceptionalValues
  ∷ keepJacobianLowerBoundUniformAcrossWhitneyChartPackets
  ∷ transportLocalGradientDataIntoCoareaStripEstimate
  ∷ keepProofA4A6NSClayAndTerminalPromotionFalse
  ∷ []

A4GradientFormulaLocalChartObligationCount : Nat
A4GradientFormulaLocalChartObligationCount =
  listLength canonicalA4GradientFormulaLocalChartObligations

A4GradientFormulaLocalChartObligationCountIs12 :
  A4GradientFormulaLocalChartObligationCount ≡ 12
A4GradientFormulaLocalChartObligationCountIs12 =
  refl

data A4GradientFormulaLocalChartBlocker : Set where
  missingConstructiveSmoothAtlasOnNonAntipodalProductSphere :
    A4GradientFormulaLocalChartBlocker
  missingNormalizeSumDerivativeInEveryChart :
    A4GradientFormulaLocalChartBlocker
  missingChartOverlapInvarianceForGradientFormula :
    A4GradientFormulaLocalChartBlocker
  missingRankNoncriticalProofForRegularOutputNormals :
    A4GradientFormulaLocalChartBlocker
  missingUniformWhitneyPacketChartConstants :
    A4GradientFormulaLocalChartBlocker
  missingCoareaConsumerProofFromLocalGradientRoute :
    A4GradientFormulaLocalChartBlocker
  downstreamCoareaStripEstimateStillBoundaryOnly :
    A4GradientFormulaLocalChartBlocker
  downstreamA4A6ClayPromotionStillBlocked :
    A4GradientFormulaLocalChartBlocker

canonicalA4GradientFormulaLocalChartBlockers :
  List A4GradientFormulaLocalChartBlocker
canonicalA4GradientFormulaLocalChartBlockers =
  missingConstructiveSmoothAtlasOnNonAntipodalProductSphere
  ∷ missingNormalizeSumDerivativeInEveryChart
  ∷ missingChartOverlapInvarianceForGradientFormula
  ∷ missingRankNoncriticalProofForRegularOutputNormals
  ∷ missingUniformWhitneyPacketChartConstants
  ∷ missingCoareaConsumerProofFromLocalGradientRoute
  ∷ downstreamCoareaStripEstimateStillBoundaryOnly
  ∷ downstreamA4A6ClayPromotionStillBlocked
  ∷ []

A4GradientFormulaLocalChartBlockerCount : Nat
A4GradientFormulaLocalChartBlockerCount =
  listLength canonicalA4GradientFormulaLocalChartBlockers

A4GradientFormulaLocalChartBlockerCountIs8 :
  A4GradientFormulaLocalChartBlockerCount ≡ 8
A4GradientFormulaLocalChartBlockerCountIs8 =
  refl

data A4GradientFormulaLocalChartStatusRow : Set where
  childCoareaBoundaryConsumed :
    A4GradientFormulaLocalChartStatusRow
  childPhiJacobianBoundaryConsumed :
    A4GradientFormulaLocalChartStatusRow
  childSardBoundaryConsumed :
    A4GradientFormulaLocalChartStatusRow
  chartAtlasObligationRecorded :
    A4GradientFormulaLocalChartStatusRow
  tangentNormalizeSumDerivativeObligationRecorded :
    A4GradientFormulaLocalChartStatusRow
  scalarGradientFormulaObligationRecorded :
    A4GradientFormulaLocalChartStatusRow
  rankNoncriticalObligationRecorded :
    A4GradientFormulaLocalChartStatusRow
  uniformChartCompatibilityObligationRecorded :
    A4GradientFormulaLocalChartStatusRow
  coareaStripRouteRecorded :
    A4GradientFormulaLocalChartStatusRow
  failClosedPromotionFlagsRecorded :
    A4GradientFormulaLocalChartStatusRow

canonicalA4GradientFormulaLocalChartStatusRows :
  List A4GradientFormulaLocalChartStatusRow
canonicalA4GradientFormulaLocalChartStatusRows =
  childCoareaBoundaryConsumed
  ∷ childPhiJacobianBoundaryConsumed
  ∷ childSardBoundaryConsumed
  ∷ chartAtlasObligationRecorded
  ∷ tangentNormalizeSumDerivativeObligationRecorded
  ∷ scalarGradientFormulaObligationRecorded
  ∷ rankNoncriticalObligationRecorded
  ∷ uniformChartCompatibilityObligationRecorded
  ∷ coareaStripRouteRecorded
  ∷ failClosedPromotionFlagsRecorded
  ∷ []

A4GradientFormulaLocalChartStatusRowCount : Nat
A4GradientFormulaLocalChartStatusRowCount =
  listLength canonicalA4GradientFormulaLocalChartStatusRows

A4GradientFormulaLocalChartStatusRowCountIs10 :
  A4GradientFormulaLocalChartStatusRowCount ≡ 10
A4GradientFormulaLocalChartStatusRowCountIs10 =
  refl

------------------------------------------------------------------------
-- Boundary receipt and fail-closed flags.

A4GradientFormulaLocalChartBoundaryRecorded : Bool
A4GradientFormulaLocalChartBoundaryRecorded =
  true

localChartAtlasConstructed : Bool
localChartAtlasConstructed =
  false

normalizeSumTangentDerivativeProved : Bool
normalizeSumTangentDerivativeProved =
  false

scalarGradientFormulaProved : Bool
scalarGradientFormulaProved =
  false

rankNoncriticalConditionProved : Bool
rankNoncriticalConditionProved =
  false

uniformChartCompatibilityProved : Bool
uniformChartCompatibilityProved =
  false

localChartRouteToCoareaStripEstimateProved : Bool
localChartRouteToCoareaStripEstimateProved =
  false

A4LeiRenTianFourierOutputCouplingProved : Bool
A4LeiRenTianFourierOutputCouplingProved =
  false

A6TriadicCompensatedLeakageIdentityProved : Bool
A6TriadicCompensatedLeakageIdentityProved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

keepsLocalChartAtlasConstructedFalse :
  localChartAtlasConstructed ≡ false
keepsLocalChartAtlasConstructedFalse =
  refl

keepsNormalizeSumTangentDerivativeProvedFalse :
  normalizeSumTangentDerivativeProved ≡ false
keepsNormalizeSumTangentDerivativeProvedFalse =
  refl

keepsScalarGradientFormulaProvedFalse :
  scalarGradientFormulaProved ≡ false
keepsScalarGradientFormulaProvedFalse =
  refl

keepsRankNoncriticalConditionProvedFalse :
  rankNoncriticalConditionProved ≡ false
keepsRankNoncriticalConditionProvedFalse =
  refl

keepsUniformChartCompatibilityProvedFalse :
  uniformChartCompatibilityProved ≡ false
keepsUniformChartCompatibilityProvedFalse =
  refl

keepsLocalChartRouteToCoareaStripEstimateProvedFalse :
  localChartRouteToCoareaStripEstimateProved ≡ false
keepsLocalChartRouteToCoareaStripEstimateProvedFalse =
  refl

keepsA4LeiRenTianFourierOutputCouplingProvedFalse :
  A4LeiRenTianFourierOutputCouplingProved ≡ false
keepsA4LeiRenTianFourierOutputCouplingProvedFalse =
  refl

keepsA6TriadicCompensatedLeakageIdentityProvedFalse :
  A6TriadicCompensatedLeakageIdentityProved ≡ false
keepsA6TriadicCompensatedLeakageIdentityProvedFalse =
  refl

keepsClayNavierStokesPromotedFalse :
  clayNavierStokesPromoted ≡ false
keepsClayNavierStokesPromotedFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

data A4GradientFormulaLocalChartClaimState : Set where
  boundaryOnlyNoAnalyticPromotion :
    A4GradientFormulaLocalChartClaimState
  proofFalseA4FalseA6FalseClayFalse :
    A4GradientFormulaLocalChartClaimState
  coareaDependencyRecordedButNotClosed :
    A4GradientFormulaLocalChartClaimState

canonicalA4GradientFormulaLocalChartClaimStates :
  List A4GradientFormulaLocalChartClaimState
canonicalA4GradientFormulaLocalChartClaimStates =
  boundaryOnlyNoAnalyticPromotion
  ∷ proofFalseA4FalseA6FalseClayFalse
  ∷ coareaDependencyRecordedButNotClosed
  ∷ []

A4GradientFormulaLocalChartClaimStateCount : Nat
A4GradientFormulaLocalChartClaimStateCount =
  listLength canonicalA4GradientFormulaLocalChartClaimStates

A4GradientFormulaLocalChartClaimStateCountIs3 :
  A4GradientFormulaLocalChartClaimStateCount ≡ 3
A4GradientFormulaLocalChartClaimStateCountIs3 =
  refl

record A4GradientFormulaLocalChartBoundaryReceipt : Set where
  field
    moduleName :
      String
    objective :
      String
    importedSupport :
      ImportedA4GradientFormulaLocalChartSupport
    target :
      A4GradientFormulaLocalChartTarget
    obligations :
      List A4GradientFormulaLocalChartObligation
    obligationCountIsCanonical :
      A4GradientFormulaLocalChartObligationCount ≡ 12
    blockers :
      List A4GradientFormulaLocalChartBlocker
    blockerCountIsCanonical :
      A4GradientFormulaLocalChartBlockerCount ≡ 8
    statusRows :
      List A4GradientFormulaLocalChartStatusRow
    statusRowCountIsCanonical :
      A4GradientFormulaLocalChartStatusRowCount ≡ 10
    claimStates :
      List A4GradientFormulaLocalChartClaimState
    claimStateCountIsCanonical :
      A4GradientFormulaLocalChartClaimStateCount ≡ 3
    boundaryRecorded :
      A4GradientFormulaLocalChartBoundaryRecorded ≡ true
    localChartAtlasStillFalse :
      localChartAtlasConstructed ≡ false
    tangentDerivativeStillFalse :
      normalizeSumTangentDerivativeProved ≡ false
    scalarGradientStillFalse :
      scalarGradientFormulaProved ≡ false
    rankNoncriticalStillFalse :
      rankNoncriticalConditionProved ≡ false
    uniformChartCompatibilityStillFalse :
      uniformChartCompatibilityProved ≡ false
    localRouteStillFalse :
      localChartRouteToCoareaStripEstimateProved ≡ false
    A4StillFalse :
      A4LeiRenTianFourierOutputCouplingProved ≡ false
    A6StillFalse :
      A6TriadicCompensatedLeakageIdentityProved ≡ false
    clayStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalStillFalse :
      terminalPromotion ≡ false

canonicalA4GradientFormulaLocalChartBoundaryReceipt :
  A4GradientFormulaLocalChartBoundaryReceipt
canonicalA4GradientFormulaLocalChartBoundaryReceipt =
  record
    { moduleName =
        "DASHI.Physics.Closure.NSA4GradientFormulaLocalChartBoundary"
    ; objective =
        "Record the local-chart gradient formula obligation for f_n(theta1,theta2)=<normalize(theta1+theta2),n> on the non-antipodal domain and route it to the A4 coarea strip estimate."
    ; importedSupport =
        canonicalImportedA4GradientFormulaLocalChartSupport
    ; target =
        canonicalA4GradientFormulaLocalChartTarget
    ; obligations =
        canonicalA4GradientFormulaLocalChartObligations
    ; obligationCountIsCanonical =
        refl
    ; blockers =
        canonicalA4GradientFormulaLocalChartBlockers
    ; blockerCountIsCanonical =
        refl
    ; statusRows =
        canonicalA4GradientFormulaLocalChartStatusRows
    ; statusRowCountIsCanonical =
        refl
    ; claimStates =
        canonicalA4GradientFormulaLocalChartClaimStates
    ; claimStateCountIsCanonical =
        refl
    ; boundaryRecorded =
        refl
    ; localChartAtlasStillFalse =
        refl
    ; tangentDerivativeStillFalse =
        refl
    ; scalarGradientStillFalse =
        refl
    ; rankNoncriticalStillFalse =
        refl
    ; uniformChartCompatibilityStillFalse =
        refl
    ; localRouteStillFalse =
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

record NSA4GradientFormulaLocalChartBoundary : Set where
  field
    receipt :
      A4GradientFormulaLocalChartBoundaryReceipt
    target :
      A4GradientFormulaLocalChartTarget
    route :
      LocalChartGradientToCoareaRoute
    coareaBoundary :
      Coarea.NSA4CoareaStripPreimageCalculationBoundary
    phiJacobianBoundary :
      PhiJacobian.NSPhiJacobianLowerBoundBoundary
    sardSlicingBoundary :
      Sard.NSSardRegularValueSlicingBoundary
    boundaryRecorded :
      A4GradientFormulaLocalChartBoundaryRecorded ≡ true
    theoremStillFalse :
      localChartRouteToCoareaStripEstimateProved ≡ false
    chartAtlasStillFalse :
      localChartAtlasConstructed ≡ false
    derivativeStillFalse :
      normalizeSumTangentDerivativeProved ≡ false
    rankStillFalse :
      rankNoncriticalConditionProved ≡ false
    compatibilityStillFalse :
      uniformChartCompatibilityProved ≡ false
    coareaStillFalse :
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

canonicalNSA4GradientFormulaLocalChartBoundary :
  NSA4GradientFormulaLocalChartBoundary
canonicalNSA4GradientFormulaLocalChartBoundary =
  record
    { receipt =
        canonicalA4GradientFormulaLocalChartBoundaryReceipt
    ; target =
        canonicalA4GradientFormulaLocalChartTarget
    ; route =
        canonicalLocalChartGradientToCoareaRoute
    ; coareaBoundary =
        Coarea.canonicalNSA4CoareaStripPreimageCalculationBoundary
    ; phiJacobianBoundary =
        PhiJacobian.canonicalNSPhiJacobianLowerBoundBoundary
    ; sardSlicingBoundary =
        Sard.canonicalNSSardRegularValueSlicingBoundary
    ; boundaryRecorded =
        refl
    ; theoremStillFalse =
        refl
    ; chartAtlasStillFalse =
        refl
    ; derivativeStillFalse =
        refl
    ; rankStillFalse =
        refl
    ; compatibilityStillFalse =
        refl
    ; coareaStillFalse =
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

