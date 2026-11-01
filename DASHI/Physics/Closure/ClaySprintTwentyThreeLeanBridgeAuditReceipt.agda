module DASHI.Physics.Closure.ClaySprintTwentyThreeLeanBridgeAuditReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintTwentyTwoThresholdFalsificationReceipt
  as Sprint22
import DASHI.Physics.Closure.SiblingMathPortingMatrix as PortMatrix

------------------------------------------------------------------------
-- Sprint 23 Lean-bridge / audit receipt.
--
-- This receipt consumes Sprint 22 and records the next formalisation layer:
-- Gate3 power-law convergence, NS geometric summability and analytic
-- physical-stretching audit, YM safe-scale correction budgets, and a Lean
-- porting boundary.  Lean-side theorem targets are useful support surfaces
-- only; they do not import external authority or promote any Clay flag.

data ClaySprintTwentyThreeStatus : Set where
  claySprintTwentyThreeLeanBridgeAuditRecorded_noPromotion :
    ClaySprintTwentyThreeStatus

data SprintTwentyThreeResult : Set where
  resultGate3PowerLawConvergenceTargetRecorded :
    SprintTwentyThreeResult

  resultNSGeometricThresholdTargetRecorded :
    SprintTwentyThreeResult

  resultNSPhysicalBridgeAuditAdded :
    SprintTwentyThreeResult

  resultYMSafeScaleCorrectionBudgetRefined :
    SprintTwentyThreeResult

  resultLeanPortTargetsQuarantinedAsSupport :
    SprintTwentyThreeResult

  resultAllPromotionFlagsRemainFalse :
    SprintTwentyThreeResult

canonicalSprintTwentyThreeResults :
  List SprintTwentyThreeResult
canonicalSprintTwentyThreeResults =
  resultGate3PowerLawConvergenceTargetRecorded
  ∷ resultNSGeometricThresholdTargetRecorded
  ∷ resultNSPhysicalBridgeAuditAdded
  ∷ resultYMSafeScaleCorrectionBudgetRefined
  ∷ resultLeanPortTargetsQuarantinedAsSupport
  ∷ resultAllPromotionFlagsRemainFalse
  ∷ []

data SprintTwentyThreeWorker : Set where
  w1Gate3PowerLawToDensityPort :
    SprintTwentyThreeWorker

  w2Gate3MoscoRecoveryConsumer :
    SprintTwentyThreeWorker

  w3NSResidueFunctionalAndQKBridge :
    SprintTwentyThreeWorker

  w4NSDynamicRatioBelowCritical :
    SprintTwentyThreeWorker

  w5YMSafeScaleCorrectionAndLeakage :
    SprintTwentyThreeWorker

  w6LeanPortGovernanceAndValidation :
    SprintTwentyThreeWorker

canonicalSprintTwentyThreeWorkers :
  List SprintTwentyThreeWorker
canonicalSprintTwentyThreeWorkers =
  w1Gate3PowerLawToDensityPort
  ∷ w2Gate3MoscoRecoveryConsumer
  ∷ w3NSResidueFunctionalAndQKBridge
  ∷ w4NSDynamicRatioBelowCritical
  ∷ w5YMSafeScaleCorrectionAndLeakage
  ∷ w6LeanPortGovernanceAndValidation
  ∷ []

data SprintTwentyThreeLeanTarget : Set where
  leanBraidThresholdCloses :
    SprintTwentyThreeLeanTarget

  leanOneThirdBeatsHalfDerivative :
    SprintTwentyThreeLeanTarget

  leanFillDistancePowerLawGoesToZero :
    SprintTwentyThreeLeanTarget

  leanBase369CarrierArithmeticSupport :
    SprintTwentyThreeLeanTarget

canonicalSprintTwentyThreeLeanTargets :
  List SprintTwentyThreeLeanTarget
canonicalSprintTwentyThreeLeanTargets =
  leanBraidThresholdCloses
  ∷ leanOneThirdBeatsHalfDerivative
  ∷ leanFillDistancePowerLawGoesToZero
  ∷ leanBase369CarrierArithmeticSupport
  ∷ []

data SprintTwentyThreeOpenGate : Set where
  gatePrunedPowerLawToCumulativeDensity :
    SprintTwentyThreeOpenGate

  gateMoscoRecoveryFromPrunedUnionDensity :
    SprintTwentyThreeOpenGate

  gateGate3MoscoNoPollutionTransfer :
    SprintTwentyThreeOpenGate

  gateBraidResidue369AnalyticFunctional :
    SprintTwentyThreeOpenGate

  gateBraidResidueControlsPhysicalStretching :
    SprintTwentyThreeOpenGate

  gateQKControlledByResidueRatio :
    SprintTwentyThreeOpenGate

  gateDynamicResidueDecayBelowCritical :
    SprintTwentyThreeOpenGate

  gateNonperturbativeCorrectionBoundAtSafeScale :
    SprintTwentyThreeOpenGate

  gateContinuumUniformRhoBoundAtSafeScale :
    SprintTwentyThreeOpenGate

  gateContinuumUniformLeakageBound :
    SprintTwentyThreeOpenGate

canonicalSprintTwentyThreeOpenGates :
  List SprintTwentyThreeOpenGate
canonicalSprintTwentyThreeOpenGates =
  gatePrunedPowerLawToCumulativeDensity
  ∷ gateMoscoRecoveryFromPrunedUnionDensity
  ∷ gateGate3MoscoNoPollutionTransfer
  ∷ gateBraidResidue369AnalyticFunctional
  ∷ gateBraidResidueControlsPhysicalStretching
  ∷ gateQKControlledByResidueRatio
  ∷ gateDynamicResidueDecayBelowCritical
  ∷ gateNonperturbativeCorrectionBoundAtSafeScale
  ∷ gateContinuumUniformRhoBoundAtSafeScale
  ∷ gateContinuumUniformLeakageBound
  ∷ []

data SprintTwentyThreeNonClaim : Set where
  leanTargetsAreNotAgdaProofImports :
    SprintTwentyThreeNonClaim

  powerLawArithmeticIsNotMoscoProof :
    SprintTwentyThreeNonClaim

  qKRatioAuditIsNotPhysicalStretchingControl :
    SprintTwentyThreeNonClaim

  transitionCountingIsNotNSDynamics :
    SprintTwentyThreeNonClaim

  safeScaleBudgetIsNotBalabanUniformity :
    SprintTwentyThreeNonClaim

  noPromotion :
    SprintTwentyThreeNonClaim

canonicalSprintTwentyThreeNonClaims :
  List SprintTwentyThreeNonClaim
canonicalSprintTwentyThreeNonClaims =
  leanTargetsAreNotAgdaProofImports
  ∷ powerLawArithmeticIsNotMoscoProof
  ∷ qKRatioAuditIsNotPhysicalStretchingControl
  ∷ transitionCountingIsNotNSDynamics
  ∷ safeScaleBudgetIsNotBalabanUniformity
  ∷ noPromotion
  ∷ []

data SprintTwentyThreePromotion : Set where

sprintTwentyThreePromotionImpossibleHere :
  SprintTwentyThreePromotion →
  ⊥
sprintTwentyThreePromotionImpossibleHere ()

resultCount : Nat
resultCount = 6

workerCount : Nat
workerCount = 6

leanTargetCount : Nat
leanTargetCount = 4

openGateCount : Nat
openGateCount = 10

nonClaimCount : Nat
nonClaimCount = 6

-- Gate3 power-law constants are inherited from Sprint 22.

gate3PowerLawAlphaNumerator : Nat
gate3PowerLawAlphaNumerator =
  Sprint22.gate3PrunedAlphaNumerator

gate3PowerLawAlphaDenominator : Nat
gate3PowerLawAlphaDenominator =
  Sprint22.gate3PrunedAlphaDenominator

gate3PowerLawCNumerator : Nat
gate3PowerLawCNumerator =
  Sprint22.gate3PrunedCNumerator

gate3PowerLawCScaleBase : Nat
gate3PowerLawCScaleBase =
  Sprint22.gate3PrunedCScale

gate3JForEpsilon0001 : Nat
gate3JForEpsilon0001 =
  Sprint22.gate3PrunedJForEpsilon0001

gate3JForEpsilon10Minus6 : Nat
gate3JForEpsilon10Minus6 =
  Sprint22.gate3PrunedJForEpsilon10Minus6

-- NS closing threshold: r * sqrt(2) < 1, stored in thousandths.

nsCriticalRatioThousandths : Nat
nsCriticalRatioThousandths =
  Sprint22.criticalRatioThousandths

nsOneThirdProductThousandths : Nat
nsOneThirdProductThousandths = 471

nsTwoThirdsProductThousandths : Nat
nsTwoThirdsProductThousandths = 943

nsSevenTenthsProductThousandths : Nat
nsSevenTenthsProductThousandths = 990

nsSixSeventhsProductThousandths : Nat
nsSixSeventhsProductThousandths = 1212

nsOneThirdTailK0ForOneMillionth : Nat
nsOneThirdTailK0ForOneMillionth =
  Sprint22.oneThirdTailK0ForOneMillionth

nsTwoThirdsTailK0ForOneMillionth : Nat
nsTwoThirdsTailK0ForOneMillionth =
  Sprint22.twoThirdsTailK0ForOneMillionth

nsSevenTenthsTailK0ForOneMillionth : Nat
nsSevenTenthsTailK0ForOneMillionth =
  Sprint22.sevenTenthsTailK0ForOneMillionth

-- YM safe-scale correction budget.

ymTargetBetaRho090TenThousandths : Nat
ymTargetBetaRho090TenThousandths =
  Sprint22.ymTargetBetaRho090TenThousandths

ymPreferredSafeScale : Nat
ymPreferredSafeScale =
  Sprint22.ymPreferredSafeScale

ymK67ToleranceTenThousandths : Nat
ymK67ToleranceTenThousandths =
  Sprint22.ymK67ToleranceTenThousandths

ymK100ToleranceTenThousandths : Nat
ymK100ToleranceTenThousandths =
  Sprint22.ymK100ToleranceTenThousandths

sprintTwentyThreeSummary : String
sprintTwentyThreeSummary =
  "Sprint 23 records Lean-bridge theorem targets as support-only, adds the NS Q_K physical-stretching audit surface, and assigns six workers across Gate3 power-law/Mosco, NS analytic residue, YM correction/leakage, and governance."

sprintTwentyThreeBoundary : String
sprintTwentyThreeBoundary =
  "This receipt is an audit and worker-assignment layer only. It does not import Lean proofs into Agda, prove Mosco recovery, prove physical NS stretching control, prove deterministic NS depletion, prove nonperturbative YM correction/rho/leakage bounds, close Gate3, solve Clay Navier-Stokes, or solve Clay Yang-Mills."

record ClaySprintTwentyThreeLeanBridgeAuditReceipt : Setω where
  field
    status :
      ClaySprintTwentyThreeStatus

    statusIsCanonical :
      status ≡ claySprintTwentyThreeLeanBridgeAuditRecorded_noPromotion

    sprintTwentyTwoReceipt :
      Sprint22.ClaySprintTwentyTwoThresholdFalsificationReceipt

    sprintTwentyTwoGate3StillFalse :
      Sprint22.gate3Closed sprintTwentyTwoReceipt ≡ false

    sprintTwentyTwoNSStillFalse :
      Sprint22.clayNavierStokesPromoted sprintTwentyTwoReceipt ≡ false

    sprintTwentyTwoYMStillFalse :
      Sprint22.clayYangMillsPromoted sprintTwentyTwoReceipt ≡ false

    siblingPortMatrix :
      PortMatrix.SiblingMathPortingMatrix

    siblingPortMatrixNoExternalAuthority :
      PortMatrix.SiblingMathPortingMatrix.acceptsExternalAuthority
        siblingPortMatrix
      ≡ false

    siblingPortMatrixNoPromotion :
      PortMatrix.SiblingMathPortingMatrix.promotesAnyGate
        siblingPortMatrix
      ≡ false

    results :
      List SprintTwentyThreeResult

    resultsAreCanonical :
      results ≡ canonicalSprintTwentyThreeResults

    resultsAreSix :
      resultCount ≡ 6

    workers :
      List SprintTwentyThreeWorker

    workersAreCanonical :
      workers ≡ canonicalSprintTwentyThreeWorkers

    workersAreSix :
      workerCount ≡ 6

    leanTargets :
      List SprintTwentyThreeLeanTarget

    leanTargetsAreCanonical :
      leanTargets ≡ canonicalSprintTwentyThreeLeanTargets

    leanTargetsAreFour :
      leanTargetCount ≡ 4

    openGates :
      List SprintTwentyThreeOpenGate

    openGatesAreCanonical :
      openGates ≡ canonicalSprintTwentyThreeOpenGates

    openGatesAreTen :
      openGateCount ≡ 10

    nonClaims :
      List SprintTwentyThreeNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalSprintTwentyThreeNonClaims

    nonClaimsAreSix :
      nonClaimCount ≡ 6

    gate3AlphaNumerator :
      Nat

    gate3AlphaNumeratorIs92 :
      gate3AlphaNumerator ≡ gate3PowerLawAlphaNumerator

    gate3AlphaDenominator :
      Nat

    gate3AlphaDenominatorIs100 :
      gate3AlphaDenominator ≡ gate3PowerLawAlphaDenominator

    gate3PowerLawC :
      Nat

    gate3PowerLawCIs07549 :
      gate3PowerLawC ≡ gate3PowerLawCNumerator

    gate3PowerLawCScale :
      Nat

    gate3PowerLawCScaleIs100000 :
      gate3PowerLawCScale ≡ gate3PowerLawCScaleBase

    gate3J0001 :
      Nat

    gate3J0001Is110 :
      gate3J0001 ≡ gate3JForEpsilon0001

    gate3J10Minus6 :
      Nat

    gate3J10Minus6Is200479 :
      gate3J10Minus6 ≡ gate3JForEpsilon10Minus6

    prunedPowerLawToDensity :
      Set

    prunedPowerLawToDensityProved :
      Bool

    prunedPowerLawToDensityProvedIsFalse :
      prunedPowerLawToDensityProved ≡ false

    moscoRecoveryFromPrunedUnionDensity :
      Set

    moscoRecoveryFromPrunedUnionDensityProved :
      Bool

    moscoRecoveryFromPrunedUnionDensityProvedIsFalse :
      moscoRecoveryFromPrunedUnionDensityProved ≡ false

    nsCriticalRatio :
      Nat

    nsCriticalRatioIs0707 :
      nsCriticalRatio ≡ nsCriticalRatioThousandths

    nsOneThirdProduct :
      Nat

    nsOneThirdProductIs0471 :
      nsOneThirdProduct ≡ nsOneThirdProductThousandths

    nsTwoThirdsProduct :
      Nat

    nsTwoThirdsProductIs0943 :
      nsTwoThirdsProduct ≡ nsTwoThirdsProductThousandths

    nsSevenTenthsProduct :
      Nat

    nsSevenTenthsProductIs0990 :
      nsSevenTenthsProduct ≡ nsSevenTenthsProductThousandths

    nsSixSeventhsProduct :
      Nat

    nsSixSeventhsProductIs1212 :
      nsSixSeventhsProduct ≡ nsSixSeventhsProductThousandths

    physicalStretchingRatioQK :
      Set

    qKControlledByResidueRatio :
      Set

    qKControlledByResidueRatioProved :
      Bool

    qKControlledByResidueRatioProvedIsFalse :
      qKControlledByResidueRatioProved ≡ false

    braidResidueControlsPhysicalStretching :
      Set

    braidResidueControlsPhysicalStretchingProved :
      Bool

    braidResidueControlsPhysicalStretchingProvedIsFalse :
      braidResidueControlsPhysicalStretchingProved ≡ false

    dynamicResidueDecayBelowCritical :
      Set

    dynamicResidueDecayBelowCriticalProved :
      Bool

    dynamicResidueDecayBelowCriticalProvedIsFalse :
      dynamicResidueDecayBelowCriticalProved ≡ false

    ymTargetBetaRho090 :
      Nat

    ymTargetBetaRho090Is141637 :
      ymTargetBetaRho090 ≡ ymTargetBetaRho090TenThousandths

    ymSafeScale :
      Nat

    ymSafeScaleIs67 :
      ymSafeScale ≡ ymPreferredSafeScale

    ymK67Tolerance :
      Nat

    ymK67ToleranceIs09180 :
      ymK67Tolerance ≡ ymK67ToleranceTenThousandths

    ymK100Tolerance :
      Nat

    ymK100ToleranceIs53911 :
      ymK100Tolerance ≡ ymK100ToleranceTenThousandths

    nonperturbativeCorrectionBoundAtSafeScale :
      Set

    nonperturbativeCorrectionBoundAtSafeScaleProved :
      Bool

    nonperturbativeCorrectionBoundAtSafeScaleProvedIsFalse :
      nonperturbativeCorrectionBoundAtSafeScaleProved ≡ false

    continuumUniformRhoBoundAtSafeScale :
      Set

    continuumUniformRhoBoundAtSafeScaleProved :
      Bool

    continuumUniformRhoBoundAtSafeScaleProvedIsFalse :
      continuumUniformRhoBoundAtSafeScaleProved ≡ false

    continuumUniformLeakageBound :
      Set

    continuumUniformLeakageBoundProved :
      Bool

    continuumUniformLeakageBoundProvedIsFalse :
      continuumUniformLeakageBoundProved ≡ false

    leanTargetsDoNotImportAuthority :
      Bool

    leanTargetsDoNotImportAuthorityIsTrue :
      leanTargetsDoNotImportAuthority ≡ true

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List SprintTwentyThreePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      SprintTwentyThreePromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ sprintTwentyThreeSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ sprintTwentyThreeBoundary

open ClaySprintTwentyThreeLeanBridgeAuditReceipt public

canonicalClaySprintTwentyThreeLeanBridgeAuditReceipt :
  ClaySprintTwentyThreeLeanBridgeAuditReceipt
canonicalClaySprintTwentyThreeLeanBridgeAuditReceipt =
  record
    { status =
        claySprintTwentyThreeLeanBridgeAuditRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; sprintTwentyTwoReceipt =
        Sprint22.canonicalClaySprintTwentyTwoThresholdFalsificationReceipt
    ; sprintTwentyTwoGate3StillFalse =
        refl
    ; sprintTwentyTwoNSStillFalse =
        refl
    ; sprintTwentyTwoYMStillFalse =
        refl
    ; siblingPortMatrix =
        PortMatrix.canonicalSiblingMathPortingMatrix
    ; siblingPortMatrixNoExternalAuthority =
        refl
    ; siblingPortMatrixNoPromotion =
        refl
    ; results =
        canonicalSprintTwentyThreeResults
    ; resultsAreCanonical =
        refl
    ; resultsAreSix =
        refl
    ; workers =
        canonicalSprintTwentyThreeWorkers
    ; workersAreCanonical =
        refl
    ; workersAreSix =
        refl
    ; leanTargets =
        canonicalSprintTwentyThreeLeanTargets
    ; leanTargetsAreCanonical =
        refl
    ; leanTargetsAreFour =
        refl
    ; openGates =
        canonicalSprintTwentyThreeOpenGates
    ; openGatesAreCanonical =
        refl
    ; openGatesAreTen =
        refl
    ; nonClaims =
        canonicalSprintTwentyThreeNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; nonClaimsAreSix =
        refl
    ; gate3AlphaNumerator =
        gate3PowerLawAlphaNumerator
    ; gate3AlphaNumeratorIs92 =
        refl
    ; gate3AlphaDenominator =
        gate3PowerLawAlphaDenominator
    ; gate3AlphaDenominatorIs100 =
        refl
    ; gate3PowerLawC =
        gate3PowerLawCNumerator
    ; gate3PowerLawCIs07549 =
        refl
    ; gate3PowerLawCScale =
        gate3PowerLawCScaleBase
    ; gate3PowerLawCScaleIs100000 =
        refl
    ; gate3J0001 =
        gate3JForEpsilon0001
    ; gate3J0001Is110 =
        refl
    ; gate3J10Minus6 =
        gate3JForEpsilon10Minus6
    ; gate3J10Minus6Is200479 =
        refl
    ; prunedPowerLawToDensity =
        ⊥
    ; prunedPowerLawToDensityProved =
        false
    ; prunedPowerLawToDensityProvedIsFalse =
        refl
    ; moscoRecoveryFromPrunedUnionDensity =
        ⊥
    ; moscoRecoveryFromPrunedUnionDensityProved =
        false
    ; moscoRecoveryFromPrunedUnionDensityProvedIsFalse =
        refl
    ; nsCriticalRatio =
        nsCriticalRatioThousandths
    ; nsCriticalRatioIs0707 =
        refl
    ; nsOneThirdProduct =
        nsOneThirdProductThousandths
    ; nsOneThirdProductIs0471 =
        refl
    ; nsTwoThirdsProduct =
        nsTwoThirdsProductThousandths
    ; nsTwoThirdsProductIs0943 =
        refl
    ; nsSevenTenthsProduct =
        nsSevenTenthsProductThousandths
    ; nsSevenTenthsProductIs0990 =
        refl
    ; nsSixSeventhsProduct =
        nsSixSeventhsProductThousandths
    ; nsSixSeventhsProductIs1212 =
        refl
    ; physicalStretchingRatioQK =
        ⊥
    ; qKControlledByResidueRatio =
        ⊥
    ; qKControlledByResidueRatioProved =
        false
    ; qKControlledByResidueRatioProvedIsFalse =
        refl
    ; braidResidueControlsPhysicalStretching =
        ⊥
    ; braidResidueControlsPhysicalStretchingProved =
        false
    ; braidResidueControlsPhysicalStretchingProvedIsFalse =
        refl
    ; dynamicResidueDecayBelowCritical =
        ⊥
    ; dynamicResidueDecayBelowCriticalProved =
        false
    ; dynamicResidueDecayBelowCriticalProvedIsFalse =
        refl
    ; ymTargetBetaRho090 =
        ymTargetBetaRho090TenThousandths
    ; ymTargetBetaRho090Is141637 =
        refl
    ; ymSafeScale =
        ymPreferredSafeScale
    ; ymSafeScaleIs67 =
        refl
    ; ymK67Tolerance =
        ymK67ToleranceTenThousandths
    ; ymK67ToleranceIs09180 =
        refl
    ; ymK100Tolerance =
        ymK100ToleranceTenThousandths
    ; ymK100ToleranceIs53911 =
        refl
    ; nonperturbativeCorrectionBoundAtSafeScale =
        ⊥
    ; nonperturbativeCorrectionBoundAtSafeScaleProved =
        false
    ; nonperturbativeCorrectionBoundAtSafeScaleProvedIsFalse =
        refl
    ; continuumUniformRhoBoundAtSafeScale =
        ⊥
    ; continuumUniformRhoBoundAtSafeScaleProved =
        false
    ; continuumUniformRhoBoundAtSafeScaleProvedIsFalse =
        refl
    ; continuumUniformLeakageBound =
        ⊥
    ; continuumUniformLeakageBoundProved =
        false
    ; continuumUniformLeakageBoundProvedIsFalse =
        refl
    ; leanTargetsDoNotImportAuthority =
        true
    ; leanTargetsDoNotImportAuthorityIsTrue =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        sprintTwentyThreePromotionImpossibleHere
    ; summary =
        sprintTwentyThreeSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        sprintTwentyThreeBoundary
    ; boundaryIsCanonical =
        refl
    }
