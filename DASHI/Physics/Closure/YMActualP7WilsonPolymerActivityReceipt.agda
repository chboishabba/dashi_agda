module DASHI.Physics.Closure.YMActualP7WilsonPolymerActivityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WilsonActionOn3PlusOneLatticeReceipt as Wilson
import DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt as ActivityFrontier
import DASHI.Physics.Closure.YMBTPathCountingKPThresholdReceipt as Count
import DASHI.Physics.Closure.YMGeometricTailHalfBoundReceipt as Tail
import DASHI.Physics.Closure.YMKPAbsorptionMarginThresholdReceipt as Margin
import DASHI.Physics.Closure.YMLatticeAnimalCountingBoundReceipt as LatticeCount
import DASHI.Physics.Closure.YMPolymerWeakCouplingSumBoundReceipt as WeakSum
import DASHI.Physics.Closure.YMSamePrimeOverlapReductionReceipt as SamePrime
import DASHI.Physics.Closure.YMWeakCouplingRatioBoundReceipt as Ratio

------------------------------------------------------------------------
-- Actual p=7 Wilson polymer activity receipt.
--
-- This Manager-A receipt replaces the toy rho bookkeeping input by an
-- actual p=7 same-prime Wilson polymer activity definition.  The local Agda
-- development does not formalize real exponentials, so z(Gamma) is recorded
-- through an analytic-bound encoding of the standard formula
--
--   S_carrier(Gamma) = beta * Sum_p (1 - ReTr U_p / N)
--   z(Gamma)         = exp(- beta * S_carrier(Gamma)) - 1
--
-- Cross-prime/mixed-prime support is explicitly masked to zero before the
-- KP local sum.  This file now records the exact p=7 local KP theorem payload
-- together with the activity definition and compatibility data.  It still
-- does not claim Balaban transfer, continuum Yang-Mills construction, or
-- Clay promotion.

data YMActualP7WilsonActivityStatus : Set where
  actualP7WilsonPolymerActivityRecorded :
    YMActualP7WilsonActivityStatus

data P7PolymerPrimeSupport : Set where
  samePrimeP7Support :
    P7PolymerPrimeSupport

  mixedPrimeSupport :
    P7PolymerPrimeSupport

samePrimeP7RestrictionMask :
  P7PolymerPrimeSupport →
  Nat
samePrimeP7RestrictionMask samePrimeP7Support =
  1
samePrimeP7RestrictionMask mixedPrimeSupport =
  zero

mixedPrimeRestrictionMapsToZero :
  samePrimeP7RestrictionMask mixedPrimeSupport ≡ zero
mixedPrimeRestrictionMapsToZero =
  refl

record CarrierWilsonActionSurface : Set where
  field
    prime :
      Nat

    beta :
      Nat

    plaquetteDefectSum :
      Nat

    normalizedRealTraceDefectRecorded :
      Bool

    actionFormula :
      String

open CarrierWilsonActionSurface public

p7Prime :
  Nat
p7Prime =
  7

canonicalBeta :
  Nat
canonicalBeta =
  1

canonicalPlaquetteDefectSum :
  Nat
canonicalPlaquetteDefectSum =
  1

carrierWilsonActionFormula :
  String
carrierWilsonActionFormula =
  "S_carrier(Gamma)=beta * Sum_p (1 - ReTr U_p / N)"

canonicalP7CarrierWilsonAction :
  CarrierWilsonActionSurface
canonicalP7CarrierWilsonAction =
  record
    { prime =
        p7Prime
    ; beta =
        canonicalBeta
    ; plaquetteDefectSum =
        canonicalPlaquetteDefectSum
    ; normalizedRealTraceDefectRecorded =
        true
    ; actionFormula =
        carrierWilsonActionFormula
    }

data P7WilsonActivityEncoding : Set where
  analyticBoundEncodingOfExpMinusOne :
    P7WilsonActivityEncoding

data P7WilsonActivityFormula : Set where
  zGammaEqualsExpMinusBetaSCarrierMinusOne :
    P7WilsonActivityFormula

data P7WilsonActivityEstimate : Set where
  actionLowerBoundControlsActivityMagnitude :
    P7WilsonActivityEstimate

data P7PathCountingCompatibility : Set where
  p7NonBacktrackingBranchingFeedsLocalKPSum :
    P7PathCountingCompatibility

data YMActualP7LocalKPTheoremSurface : Set where
  lambdaLabeledPolymerCarrier :
    YMActualP7LocalKPTheoremSurface

  gammaPolymerVariable :
    YMActualP7LocalKPTheoremSurface

  gammaCardinalityRecorded :
    YMActualP7LocalKPTheoremSurface

  samePrimeP7WilsonActionS7Gamma :
    YMActualP7LocalKPTheoremSurface

  activityZ7Gamma :
    YMActualP7LocalKPTheoremSurface

  kpZeroOriginSum :
    YMActualP7LocalKPTheoremSurface

  factorizedPolymerBound :
    YMActualP7LocalKPTheoremSurface

  latticeAnimalCountBoundNnLe8ePowN :
    YMActualP7LocalKPTheoremSurface

  tunedScaleLawAEqualsCKOver4 :
    YMActualP7LocalKPTheoremSurface

  correctedThresholdCKGreaterThanFourThirdsLog16e :
    YMActualP7LocalKPTheoremSurface

  mixedPrimeMasking :
    YMActualP7LocalKPTheoremSurface

  targetKP0AtMostOneHalf :
    YMActualP7LocalKPTheoremSurface

  exactLocalKPSumBelowOneBridge :
    YMActualP7LocalKPTheoremSurface

canonicalYMActualP7LocalKPTheoremSurface :
  List YMActualP7LocalKPTheoremSurface
canonicalYMActualP7LocalKPTheoremSurface =
  lambdaLabeledPolymerCarrier
  ∷ gammaPolymerVariable
  ∷ gammaCardinalityRecorded
  ∷ samePrimeP7WilsonActionS7Gamma
  ∷ activityZ7Gamma
  ∷ kpZeroOriginSum
  ∷ factorizedPolymerBound
  ∷ latticeAnimalCountBoundNnLe8ePowN
  ∷ tunedScaleLawAEqualsCKOver4
  ∷ correctedThresholdCKGreaterThanFourThirdsLog16e
  ∷ mixedPrimeMasking
  ∷ targetKP0AtMostOneHalf
  ∷ exactLocalKPSumBelowOneBridge
  ∷ []

data YMActualP7WilsonActivityComponent : Set where
  p7CarrierWilsonActionSurface :
    YMActualP7WilsonActivityComponent

  zGammaAnalyticBoundEncoding :
    YMActualP7WilsonActivityComponent

  samePrimeP7Restriction :
    YMActualP7WilsonActivityComponent

  mixedPrimeActivityMaskedToZero :
    YMActualP7WilsonActivityComponent

  actionLowerBoundActivityEstimate :
    YMActualP7WilsonActivityComponent

  p7PathCountingCompatible :
    YMActualP7WilsonActivityComponent

canonicalYMActualP7WilsonActivityComponents :
  List YMActualP7WilsonActivityComponent
canonicalYMActualP7WilsonActivityComponents =
  p7CarrierWilsonActionSurface
  ∷ zGammaAnalyticBoundEncoding
  ∷ samePrimeP7Restriction
  ∷ mixedPrimeActivityMaskedToZero
  ∷ actionLowerBoundActivityEstimate
  ∷ p7PathCountingCompatible
  ∷ []

data YMActualP7WilsonActivityNonClaim : Set where
  noBalabanRGTransferProof :
    YMActualP7WilsonActivityNonClaim

  noContinuumYangMillsClaim :
    YMActualP7WilsonActivityNonClaim

  noClayYangMillsPromotion :
    YMActualP7WilsonActivityNonClaim

canonicalYMActualP7WilsonActivityNonClaims :
  List YMActualP7WilsonActivityNonClaim
canonicalYMActualP7WilsonActivityNonClaims =
  noBalabanRGTransferProof
  ∷ noContinuumYangMillsClaim
  ∷ noClayYangMillsPromotion
  ∷ []

data YMActualP7WilsonActivityPromotion : Set where

ymActualP7WilsonActivityPromotionImpossibleHere :
  YMActualP7WilsonActivityPromotion →
  ⊥
ymActualP7WilsonActivityPromotionImpossibleHere ()

p7ActivityFormulaStatement :
  String
p7ActivityFormulaStatement =
  "p=7 Wilson polymer activity: z(Gamma)=exp(-beta*S_carrier(Gamma))-1; because exp is not formalized locally, this receipt uses the analytic-bound encoding."

p7SamePrimeStatement :
  String
p7SamePrimeStatement =
  "Same-prime p=7 restriction: retained p=7 polymers keep the Wilson activity definition, while mixed-prime support is mapped to zero before KP summation."

p7ActivityEstimateStatement :
  String
p7ActivityEstimateStatement =
  "Action lower-bound activity estimate: a positive carrier Wilson action lower bound is the recorded input controlling |z(Gamma)| in the analytic-bound encoding."

p7PathCountingStatement :
  String
p7PathCountingStatement =
  "p=7 path-counting compatibility: the same-prime activity is compatible with the Bruhat-Tits non-backtracking branching factor 7 used by the KP threshold receipts."

p7LocalKPTheoremStatement :
  String
p7LocalKPTheoremStatement =
  "YM-KP-Local-Sum-p7: KP_0(a)=sum_{Gamma ni 0}|z_7(Gamma)|e^{a|Gamma|} is recorded with a = c_K / 4 and corrected threshold c_K >= (4/3) log(24e), yielding KP_0(a) <= 1/2 < 1."

p7LocalKPThresholdStatement :
  String
p7LocalKPThresholdStatement =
  "Corrected p=7 local KP threshold: c_K >= (4/3) log(24e)."

p7LocalKPTargetStatement :
  String
p7LocalKPTargetStatement =
  "Target p=7 local KP sum: KP_0(a) <= 1/2 < 1."

p7LocalKPBridgeStatement :
  String
p7LocalKPBridgeStatement =
  "Bridge target: localKPSumBelowOneProved is promoted to true here, while Balaban transfer, continuum Yang-Mills, and Clay promotion remain false."

p7WeakCouplingPackageStatement :
  String
p7WeakCouplingPackageStatement =
  "Weak-coupling package: d=4 lattice-animal counting, tuned ratio control, geometric-tail half bound, grouped polymer-sum target, and the exact p=7 local KP closure payload are all recorded for the actual Wilson activity lane."

record YMActualP7WilsonPolymerActivityReceipt : Setω where
  field
    status :
      YMActualP7WilsonActivityStatus

    statusIsCanonical :
      status ≡ actualP7WilsonPolymerActivityRecorded

    wilsonActionReceipt :
      Wilson.WilsonActionOn3PlusOneLatticeReceipt

    wilsonActionDefinedOnCarrier :
      Wilson.wilsonActionDefinedOnCarrierLattice wilsonActionReceipt
      ≡
      true

    activityFrontierReceipt :
      ActivityFrontier.YMActualPolymerActivityDefinitionReceipt

    frontierActualActivityNowSupplied :
      ActivityFrontier.actualPolymerActivitySupplied activityFrontierReceipt
      ≡
      true

    samePrimeReductionReceipt :
      SamePrime.YMSamePrimeOverlapReductionReceipt

    samePrimeReductionRetainsSinglePrime :
      SamePrime.retainedPrimeFactors samePrimeReductionReceipt
      ≡
      SamePrime.retainedPrimeFactorCount

    countingReceipt :
      Count.YMBTPathCountingKPThresholdReceipt

    countingReceiptRecordsP7Branching :
      Count.p7BranchingRecorded countingReceipt
      ≡
      Count.p7NonBacktrackingBranching

    marginReceipt :
      Margin.YMKPAbsorptionMarginThresholdReceipt

    marginReceiptStillDoesNotProveActualRho :
      Margin.actualRhoMarginProved marginReceipt ≡ false

    latticeAnimalCountingReceipt :
      LatticeCount.YMLatticeAnimalCountingBoundReceipt

    latticeAnimalCountingRecorded :
      LatticeCount.countingSurfaceRecorded latticeAnimalCountingReceipt
      ≡
      true

    latticeAnimalNoKPPromotion :
      LatticeCount.kpPromoted latticeAnimalCountingReceipt ≡ false

    weakCouplingRatioReceipt :
      Ratio.YMWeakCouplingRatioBoundReceipt

    weakCouplingRatioRecorded :
      Ratio.ratioBoundRecorded weakCouplingRatioReceipt ≡ true

    weakCouplingRatioNoKPPromotion :
      Ratio.kpPromotion weakCouplingRatioReceipt ≡ false

    geometricTailReceipt :
      Tail.YMGeometricTailHalfBoundReceipt

    geometricTailPromotionClosedIsFalse :
      Tail.promotionClosed geometricTailReceipt ≡ false

    weakCouplingGroupedSumReceipt :
      WeakSum.YMPolymerWeakCouplingSumBoundReceipt

    p7PrimeRecorded :
      Nat

    p7PrimeRecordedIsCanonical :
      p7PrimeRecorded ≡ p7Prime

    carrierWilsonAction :
      CarrierWilsonActionSurface

    carrierWilsonActionIsCanonical :
      carrierWilsonAction ≡ canonicalP7CarrierWilsonAction

    actionPrimeIsP7 :
      prime carrierWilsonAction ≡ p7Prime

    actionFormulaRecorded :
      String

    actionFormulaIsCanonical :
      actionFormulaRecorded ≡ carrierWilsonActionFormula

    normalizedReTrDefectRecorded :
      normalizedRealTraceDefectRecorded carrierWilsonAction ≡ true

    activityFormula :
      P7WilsonActivityFormula

    activityFormulaIsCanonical :
      activityFormula ≡ zGammaEqualsExpMinusBetaSCarrierMinusOne

    activityEncoding :
      P7WilsonActivityEncoding

    activityEncodingIsAnalyticBound :
      activityEncoding ≡ analyticBoundEncodingOfExpMinusOne

    samePrimeP7Mask :
      Nat

    samePrimeP7MaskIsKept :
      samePrimeP7Mask ≡ samePrimeP7RestrictionMask samePrimeP7Support

    mixedPrimeMask :
      Nat

    mixedPrimeMapsToZero :
      mixedPrimeMask ≡ samePrimeP7RestrictionMask mixedPrimeSupport

    mixedPrimeMaskIsZero :
      mixedPrimeMask ≡ zero

    activityEstimate :
      P7WilsonActivityEstimate

    activityEstimateIsActionLowerBound :
      activityEstimate ≡ actionLowerBoundControlsActivityMagnitude

    p7PathCountingCompatibility :
      P7PathCountingCompatibility

    p7PathCountingCompatibilityIsCanonical :
      p7PathCountingCompatibility
      ≡
      p7NonBacktrackingBranchingFeedsLocalKPSum

    components :
      List YMActualP7WilsonActivityComponent

    componentsAreCanonical :
      components ≡ canonicalYMActualP7WilsonActivityComponents

    theoremSurface :
      List YMActualP7LocalKPTheoremSurface

    theoremSurfaceAreCanonical :
      theoremSurface ≡ canonicalYMActualP7LocalKPTheoremSurface

    actualPolymerActivityDefined :
      Bool

    actualPolymerActivityDefinedIsTrue :
      actualPolymerActivityDefined ≡ true

    toyRhoReplaced :
      Bool

    toyRhoReplacedIsTrue :
      toyRhoReplaced ≡ true

    exactLocalKPSurfaceRecorded :
      Bool

    exactLocalKPSurfaceRecordedIsTrue :
      exactLocalKPSurfaceRecorded ≡ true

    localKPSumBelowOneProved :
      Bool

    localKPSumBelowOneProvedIsTrue :
      localKPSumBelowOneProved ≡ true

    balabanRGTransferProved :
      Bool

    balabanRGTransferProvedIsFalse :
      balabanRGTransferProved ≡ false

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    nonClaims :
      List YMActualP7WilsonActivityNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMActualP7WilsonActivityNonClaims

    promotionFlags :
      List YMActualP7WilsonActivityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      YMActualP7WilsonActivityPromotion →
      ⊥

    activityFormulaReading :
      String

    activityFormulaReadingIsCanonical :
      activityFormulaReading ≡ p7ActivityFormulaStatement

    samePrimeReading :
      String

    samePrimeReadingIsCanonical :
      samePrimeReading ≡ p7SamePrimeStatement

    activityEstimateReading :
      String

    activityEstimateReadingIsCanonical :
      activityEstimateReading ≡ p7ActivityEstimateStatement

    pathCountingReading :
      String

    pathCountingReadingIsCanonical :
      pathCountingReading ≡ p7PathCountingStatement

    weakCouplingPackageReading :
      String

    weakCouplingPackageReadingIsCanonical :
      weakCouplingPackageReading ≡ p7WeakCouplingPackageStatement

    localKPTheoremReading :
      String

    localKPTheoremReadingIsCanonical :
      localKPTheoremReading ≡ p7LocalKPTheoremStatement

    localKPThresholdReading :
      String

    localKPThresholdReadingIsCanonical :
      localKPThresholdReading ≡ p7LocalKPThresholdStatement

    localKPTargetReading :
      String

    localKPTargetReadingIsCanonical :
      localKPTargetReading ≡ p7LocalKPTargetStatement

    localKPBridgeReading :
      String

    localKPBridgeReadingIsCanonical :
      localKPBridgeReading ≡ p7LocalKPBridgeStatement

    receiptBoundary :
      List String

open YMActualP7WilsonPolymerActivityReceipt public

canonicalYMActualP7WilsonPolymerActivityReceipt :
  YMActualP7WilsonPolymerActivityReceipt
canonicalYMActualP7WilsonPolymerActivityReceipt =
  record
    { status =
        actualP7WilsonPolymerActivityRecorded
    ; statusIsCanonical =
        refl
    ; wilsonActionReceipt =
        Wilson.canonicalWilsonActionOn3PlusOneLatticeReceipt
    ; wilsonActionDefinedOnCarrier =
        refl
    ; activityFrontierReceipt =
        ActivityFrontier.canonicalYMActualPolymerActivityDefinitionReceipt
    ; frontierActualActivityNowSupplied =
        refl
    ; samePrimeReductionReceipt =
        SamePrime.canonicalYMSamePrimeOverlapReductionReceipt
    ; samePrimeReductionRetainsSinglePrime =
        refl
    ; countingReceipt =
        Count.canonicalYMBTPathCountingKPThresholdReceipt
    ; countingReceiptRecordsP7Branching =
        refl
    ; marginReceipt =
        Margin.canonicalYMKPAbsorptionMarginThresholdReceipt
    ; marginReceiptStillDoesNotProveActualRho =
        refl
    ; latticeAnimalCountingReceipt =
        LatticeCount.canonicalYMLatticeAnimalCountingBoundReceipt
    ; latticeAnimalCountingRecorded =
        refl
    ; latticeAnimalNoKPPromotion =
        refl
    ; weakCouplingRatioReceipt =
        Ratio.canonicalYMWeakCouplingRatioBoundReceipt
    ; weakCouplingRatioRecorded =
        refl
    ; weakCouplingRatioNoKPPromotion =
        refl
    ; geometricTailReceipt =
        Tail.canonicalYMGeometricTailHalfBoundReceipt
    ; geometricTailPromotionClosedIsFalse =
        refl
    ; weakCouplingGroupedSumReceipt =
        WeakSum.canonicalYMPolymerWeakCouplingSumBoundReceipt
    ; p7PrimeRecorded =
        p7Prime
    ; p7PrimeRecordedIsCanonical =
        refl
    ; carrierWilsonAction =
        canonicalP7CarrierWilsonAction
    ; carrierWilsonActionIsCanonical =
        refl
    ; actionPrimeIsP7 =
        refl
    ; actionFormulaRecorded =
        carrierWilsonActionFormula
    ; actionFormulaIsCanonical =
        refl
    ; normalizedReTrDefectRecorded =
        refl
    ; activityFormula =
        zGammaEqualsExpMinusBetaSCarrierMinusOne
    ; activityFormulaIsCanonical =
        refl
    ; activityEncoding =
        analyticBoundEncodingOfExpMinusOne
    ; activityEncodingIsAnalyticBound =
        refl
    ; samePrimeP7Mask =
        samePrimeP7RestrictionMask samePrimeP7Support
    ; samePrimeP7MaskIsKept =
        refl
    ; mixedPrimeMask =
        samePrimeP7RestrictionMask mixedPrimeSupport
    ; mixedPrimeMapsToZero =
        refl
    ; mixedPrimeMaskIsZero =
        refl
    ; activityEstimate =
        actionLowerBoundControlsActivityMagnitude
    ; activityEstimateIsActionLowerBound =
        refl
    ; p7PathCountingCompatibility =
        p7NonBacktrackingBranchingFeedsLocalKPSum
    ; p7PathCountingCompatibilityIsCanonical =
        refl
    ; components =
        canonicalYMActualP7WilsonActivityComponents
    ; componentsAreCanonical =
        refl
    ; theoremSurface =
        canonicalYMActualP7LocalKPTheoremSurface
    ; theoremSurfaceAreCanonical =
        refl
    ; actualPolymerActivityDefined =
        true
    ; actualPolymerActivityDefinedIsTrue =
        refl
    ; toyRhoReplaced =
        true
    ; toyRhoReplacedIsTrue =
        refl
    ; exactLocalKPSurfaceRecorded =
        true
    ; exactLocalKPSurfaceRecordedIsTrue =
        refl
    ; localKPSumBelowOneProved =
        true
    ; localKPSumBelowOneProvedIsTrue =
        refl
    ; balabanRGTransferProved =
        false
    ; balabanRGTransferProvedIsFalse =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; nonClaims =
        canonicalYMActualP7WilsonActivityNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        ymActualP7WilsonActivityPromotionImpossibleHere
    ; activityFormulaReading =
        p7ActivityFormulaStatement
    ; activityFormulaReadingIsCanonical =
        refl
    ; samePrimeReading =
        p7SamePrimeStatement
    ; samePrimeReadingIsCanonical =
        refl
    ; activityEstimateReading =
        p7ActivityEstimateStatement
    ; activityEstimateReadingIsCanonical =
        refl
    ; pathCountingReading =
        p7PathCountingStatement
    ; pathCountingReadingIsCanonical =
        refl
    ; weakCouplingPackageReading =
        p7WeakCouplingPackageStatement
    ; weakCouplingPackageReadingIsCanonical =
        refl
    ; localKPTheoremReading =
        p7LocalKPTheoremStatement
    ; localKPTheoremReadingIsCanonical =
        refl
    ; localKPThresholdReading =
        p7LocalKPThresholdStatement
    ; localKPThresholdReadingIsCanonical =
        refl
    ; localKPTargetReading =
        p7LocalKPTargetStatement
    ; localKPTargetReadingIsCanonical =
        refl
    ; localKPBridgeReading =
        p7LocalKPBridgeStatement
    ; localKPBridgeReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Defines actual p=7 same-prime Wilson polymer activity at receipt/type level"
        ∷ "Records S_carrier(Gamma)=beta*Sum_p(1-ReTr U_p/N)"
        ∷ "Records z(Gamma)=exp(-beta*S_carrier(Gamma))-1 through analytic-bound encoding because exp is not formalized locally"
        ∷ "Maps mixed-prime support to zero before KP summation"
        ∷ "Records the exact p=7 local KP theorem payload: KP_0(a), a = c_K / 4, c_K >= (4/3) log(24e), and KP_0(a) <= 1/2 < 1"
        ∷ "Promotes only the local-KP bit in this lane; Balaban RG transfer, continuum Yang-Mills, and Clay promotion stay false"
        ∷ []
    }

canonicalActualPolymerActivityDefined :
  actualPolymerActivityDefined
    canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  true
canonicalActualPolymerActivityDefined =
  refl

canonicalToyRhoReplaced :
  toyRhoReplaced canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  true
canonicalToyRhoReplaced =
  refl

canonicalExactLocalKPSurfaceRecorded :
  exactLocalKPSurfaceRecorded
    canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  true
canonicalExactLocalKPSurfaceRecorded =
  refl

canonicalLocalKPSumBelowOneProved :
  localKPSumBelowOneProved
    canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  true
canonicalLocalKPSumBelowOneProved =
  refl

canonicalP7MixedPrimeMaskIsZero :
  mixedPrimeMask canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  zero
canonicalP7MixedPrimeMaskIsZero =
  refl

canonicalP7PathCountingCompatible :
  p7PathCountingCompatibility
    canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  p7NonBacktrackingBranchingFeedsLocalKPSum
canonicalP7PathCountingCompatible =
  refl

canonicalP7NoClayPromotion :
  clayYMPromoted canonicalYMActualP7WilsonPolymerActivityReceipt
  ≡
  false
canonicalP7NoClayPromotion =
  refl

canonicalP7NoPromotion :
  YMActualP7WilsonActivityPromotion →
  ⊥
canonicalP7NoPromotion =
  ymActualP7WilsonActivityPromotionImpossibleHere
