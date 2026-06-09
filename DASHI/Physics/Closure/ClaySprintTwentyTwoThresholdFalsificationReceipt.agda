module DASHI.Physics.Closure.ClaySprintTwentyTwoThresholdFalsificationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintTwentyOneFrontierAuditReceipt
  as Sprint21

------------------------------------------------------------------------
-- Sprint 22 threshold / falsification receipt.
--
-- This receipt records the next useful threshold calculations after Sprint
-- 21: Gate3 pruned fill-distance power-law witnesses, NS braid-residue tail
-- thresholds, YM nonperturbative correction tolerances, and T7A quarantine.
-- These are falsification/audit targets only; they do not promote Gate3,
-- Navier-Stokes, or Yang-Mills.

data ClaySprintTwentyTwoStatus : Set where
  claySprintTwentyTwoThresholdFalsificationRecorded_noPromotion :
    ClaySprintTwentyTwoStatus

data SprintTwentyTwoResult : Set where
  gate3PrunedPowerLawAlpha092Anchored :
    SprintTwentyTwoResult

  gate3PowerLawWitnessTableRecorded :
    SprintTwentyTwoResult

  nsTailDepthThresholdTableRecorded :
    SprintTwentyTwoResult

  nsStaticLerayRouteRemainsKilled :
    SprintTwentyTwoResult

  ymExpandedCorrectionToleranceTableRecorded :
    SprintTwentyTwoResult

  t7aThresholdQuarantined :
    SprintTwentyTwoResult

  allPromotionFlagsRemainFalse :
    SprintTwentyTwoResult

canonicalSprintTwentyTwoResults :
  List SprintTwentyTwoResult
canonicalSprintTwentyTwoResults =
  gate3PrunedPowerLawAlpha092Anchored
  ∷ gate3PowerLawWitnessTableRecorded
  ∷ nsTailDepthThresholdTableRecorded
  ∷ nsStaticLerayRouteRemainsKilled
  ∷ ymExpandedCorrectionToleranceTableRecorded
  ∷ t7aThresholdQuarantined
  ∷ allPromotionFlagsRemainFalse
  ∷ []

data SprintTwentyTwoWorker : Set where
  w1Gate3PrunedPowerLawAndMosco :
    SprintTwentyTwoWorker

  w2NSTailThresholdAndRatioAudit :
    SprintTwentyTwoWorker

  w3NSPhysicalStretchingBridge :
    SprintTwentyTwoWorker

  w4YMSafeScaleCorrectionBudget :
    SprintTwentyTwoWorker

  w5T7AQuarantineAndKPGovernance :
    SprintTwentyTwoWorker

  w6IntegrationValidationAndPromotionAudit :
    SprintTwentyTwoWorker

canonicalSprintTwentyTwoWorkers :
  List SprintTwentyTwoWorker
canonicalSprintTwentyTwoWorkers =
  w1Gate3PrunedPowerLawAndMosco
  ∷ w2NSTailThresholdAndRatioAudit
  ∷ w3NSPhysicalStretchingBridge
  ∷ w4YMSafeScaleCorrectionBudget
  ∷ w5T7AQuarantineAndKPGovernance
  ∷ w6IntegrationValidationAndPromotionAudit
  ∷ []

data SprintTwentyTwoOpenGate : Set where
  gatePruningPreservesCumulativeFillDistancePowerLaw :
    SprintTwentyTwoOpenGate

  gateMoscoRecoveryFromPrunedUnionDensity :
    SprintTwentyTwoOpenGate

  gateBraidResidueControlsPhysicalStretching :
    SprintTwentyTwoOpenGate

  gateDynamicBraidResidueDecayForNSBelowCritical :
    SprintTwentyTwoOpenGate

  gateCoherentTubeExclusion :
    SprintTwentyTwoOpenGate

  gateNonperturbativeCorrectionBoundAtSafeScale :
    SprintTwentyTwoOpenGate

  gateContinuumUniformRhoBoundAtSafeScale :
    SprintTwentyTwoOpenGate

  gateContinuumUniformLeakageBound :
    SprintTwentyTwoOpenGate

canonicalSprintTwentyTwoOpenGates :
  List SprintTwentyTwoOpenGate
canonicalSprintTwentyTwoOpenGates =
  gatePruningPreservesCumulativeFillDistancePowerLaw
  ∷ gateMoscoRecoveryFromPrunedUnionDensity
  ∷ gateBraidResidueControlsPhysicalStretching
  ∷ gateDynamicBraidResidueDecayForNSBelowCritical
  ∷ gateCoherentTubeExclusion
  ∷ gateNonperturbativeCorrectionBoundAtSafeScale
  ∷ gateContinuumUniformRhoBoundAtSafeScale
  ∷ gateContinuumUniformLeakageBound
  ∷ []

data SprintTwentyTwoNonClaim : Set where
  positiveAlphaTableIsNotMoscoProof :
    SprintTwentyTwoNonClaim

  nsTailTableIsNotPDEDepletion :
    SprintTwentyTwoNonClaim

  nsScalingObstructionDoesNotSolveNS :
    SprintTwentyTwoNonClaim

  oneLoopToleranceIsNotBalabanProof :
    SprintTwentyTwoNonClaim

  t7aThresholdDoesNotPromoteYM :
    SprintTwentyTwoNonClaim

  noPromotion :
    SprintTwentyTwoNonClaim

canonicalSprintTwentyTwoNonClaims :
  List SprintTwentyTwoNonClaim
canonicalSprintTwentyTwoNonClaims =
  positiveAlphaTableIsNotMoscoProof
  ∷ nsTailTableIsNotPDEDepletion
  ∷ nsScalingObstructionDoesNotSolveNS
  ∷ oneLoopToleranceIsNotBalabanProof
  ∷ t7aThresholdDoesNotPromoteYM
  ∷ noPromotion
  ∷ []

data SprintTwentyTwoPromotion : Set where

sprintTwentyTwoPromotionImpossibleHere :
  SprintTwentyTwoPromotion →
  ⊥
sprintTwentyTwoPromotionImpossibleHere ()

resultCount : Nat
resultCount = 7

workerCount : Nat
workerCount = 6

openGateCount : Nat
openGateCount = 8

nonClaimCount : Nat
nonClaimCount = 6

-- Gate3 pruned fill-distance power law.
-- alpha = 0.92 is represented as 92 / 100.
-- C ~= 0.07549 is represented as 7549 / 100000.

gate3PrunedAlphaNumerator : Nat
gate3PrunedAlphaNumerator = 92

gate3PrunedAlphaDenominator : Nat
gate3PrunedAlphaDenominator = 100

gate3PrunedCScale : Nat
gate3PrunedCScale = 100000

gate3PrunedCNumerator : Nat
gate3PrunedCNumerator = 7549

gate3PrunedJForEpsilon001 : Nat
gate3PrunedJForEpsilon001 = 9

gate3PrunedJForEpsilon0001 : Nat
gate3PrunedJForEpsilon0001 = 110

gate3PrunedJForEpsilon00001 : Nat
gate3PrunedJForEpsilon00001 = 1344

gate3PrunedJForEpsilon10Minus6 : Nat
gate3PrunedJForEpsilon10Minus6 = 200479

-- NS residue tail-depth thresholds.  K0 values are recorded only for regimes
-- with r * sqrt(2) < 1.

criticalRatioThousandths : Nat
criticalRatioThousandths = 707

oneThirdTailK0ForOneHundredth : Nat
oneThirdTailK0ForOneHundredth = 7

oneThirdTailK0ForOneMillionth : Nat
oneThirdTailK0ForOneMillionth = 20

oneHalfTailK0ForOneHundredth : Nat
oneHalfTailK0ForOneHundredth = 17

oneHalfTailK0ForOneMillionth : Nat
oneHalfTailK0ForOneMillionth = 44

twoThirdsTailK0ForOneHundredth : Nat
twoThirdsTailK0ForOneHundredth = 127

twoThirdsTailK0ForOneMillionth : Nat
twoThirdsTailK0ForOneMillionth = 284

sevenTenthsTailK0ForOneHundredth : Nat
sevenTenthsTailK0ForOneHundredth = 912

sevenTenthsTailK0ForOneMillionth : Nat
sevenTenthsTailK0ForOneMillionth = 1824

sixSeventhsDivergesRecorded : Bool
sixSeventhsDivergesRecorded = true

coherentTubeDivergesRecorded : Bool
coherentTubeDivergesRecorded = true

-- YM expanded correction budget, beta scaled by 10000.

ymTargetBetaRho090TenThousandths : Nat
ymTargetBetaRho090TenThousandths = 141637

ymOneLoopIncrementTenThousandths : Nat
ymOneLoopIncrementTenThousandths = 1355

ymK60BetaOneLoopTenThousandths : Nat
ymK60BetaOneLoopTenThousandths = 141329

ymK60ShortfallTenThousandths : Nat
ymK60ShortfallTenThousandths = 308

ymK61BetaOneLoopTenThousandths : Nat
ymK61BetaOneLoopTenThousandths = 142685

ymK61ToleranceTenThousandths : Nat
ymK61ToleranceTenThousandths = 1048

ymK62BetaOneLoopTenThousandths : Nat
ymK62BetaOneLoopTenThousandths = 144040

ymK62ToleranceTenThousandths : Nat
ymK62ToleranceTenThousandths = 2403

ymK65BetaOneLoopTenThousandths : Nat
ymK65BetaOneLoopTenThousandths = 148107

ymK65ToleranceTenThousandths : Nat
ymK65ToleranceTenThousandths = 6469

ymK67BetaOneLoopTenThousandths : Nat
ymK67BetaOneLoopTenThousandths = 150818

ymK67ToleranceTenThousandths : Nat
ymK67ToleranceTenThousandths = 9180

ymK70BetaOneLoopTenThousandths : Nat
ymK70BetaOneLoopTenThousandths = 154884

ymK70ToleranceTenThousandths : Nat
ymK70ToleranceTenThousandths = 13247

ymK75BetaOneLoopTenThousandths : Nat
ymK75BetaOneLoopTenThousandths = 161662

ymK75ToleranceTenThousandths : Nat
ymK75ToleranceTenThousandths = 20024

ymK80BetaOneLoopTenThousandths : Nat
ymK80BetaOneLoopTenThousandths = 168439

ymK80ToleranceTenThousandths : Nat
ymK80ToleranceTenThousandths = 26802

ymK90BetaOneLoopTenThousandths : Nat
ymK90BetaOneLoopTenThousandths = 181994

ymK90ToleranceTenThousandths : Nat
ymK90ToleranceTenThousandths = 40357

ymK100BetaOneLoopTenThousandths : Nat
ymK100BetaOneLoopTenThousandths = 195549

ymK100ToleranceTenThousandths : Nat
ymK100ToleranceTenThousandths = 53911

ymPreferredSafeScale : Nat
ymPreferredSafeScale = 67

-- T7A bookkeeping, beta scaled by 10000.

t7aBetaStarTenThousandths : Nat
t7aBetaStarTenThousandths = 165556

t7aSmallDepthCutoff : Nat
t7aSmallDepthCutoff = 3

t7aCrossoverDepth : Nat
t7aCrossoverDepth = 4

sprintTwentyTwoSummary : String
sprintTwentyTwoSummary =
  "Sprint 22 records threshold/falsification calculations: Gate3 pruned fill-distance alpha=0.92 witnesses, NS residue tail-depth thresholds, YM expanded correction budgets at safe scale k>=67, and T7A quarantine. No promotion flags flip."

sprintTwentyTwoBoundary : String
sprintTwentyTwoBoundary =
  "This receipt records numeric thresholds and worker assignments only. It does not prove Mosco recovery, physical NS residue control, deterministic NS depletion, nonperturbative YM correction/rho/leakage bounds, T7A-to-YM transfer, Gate3 closure, Clay Navier-Stokes, or Clay Yang-Mills."

record ClaySprintTwentyTwoThresholdFalsificationReceipt : Setω where
  field
    status :
      ClaySprintTwentyTwoStatus

    statusIsCanonical :
      status ≡ claySprintTwentyTwoThresholdFalsificationRecorded_noPromotion

    sprintTwentyOneReceipt :
      Sprint21.ClaySprintTwentyOneFrontierAuditReceipt

    sprintTwentyOneGate3StillFalse :
      Sprint21.gate3Closed sprintTwentyOneReceipt ≡ false

    sprintTwentyOneNSStillFalse :
      Sprint21.clayNavierStokesPromoted sprintTwentyOneReceipt ≡ false

    sprintTwentyOneYMStillFalse :
      Sprint21.clayYangMillsPromoted sprintTwentyOneReceipt ≡ false

    results :
      List SprintTwentyTwoResult

    resultsAreCanonical :
      results ≡ canonicalSprintTwentyTwoResults

    resultsAreSeven :
      resultCount ≡ 7

    workers :
      List SprintTwentyTwoWorker

    workersAreCanonical :
      workers ≡ canonicalSprintTwentyTwoWorkers

    workersAreSix :
      workerCount ≡ 6

    openGates :
      List SprintTwentyTwoOpenGate

    openGatesAreCanonical :
      openGates ≡ canonicalSprintTwentyTwoOpenGates

    openGatesAreEight :
      openGateCount ≡ 8

    nonClaims :
      List SprintTwentyTwoNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalSprintTwentyTwoNonClaims

    nonClaimsAreSix :
      nonClaimCount ≡ 6

    gate3AlphaNumerator :
      Nat

    gate3AlphaNumeratorIs92 :
      gate3AlphaNumerator ≡ gate3PrunedAlphaNumerator

    gate3AlphaDenominator :
      Nat

    gate3AlphaDenominatorIs100 :
      gate3AlphaDenominator ≡ gate3PrunedAlphaDenominator

    gate3PowerLawC :
      Nat

    gate3PowerLawCIs07549 :
      gate3PowerLawC ≡ gate3PrunedCNumerator

    gate3PowerLawCScale :
      Nat

    gate3PowerLawCScaleIs100000 :
      gate3PowerLawCScale ≡ gate3PrunedCScale

    gate3J001 :
      Nat

    gate3J001Is9 :
      gate3J001 ≡ gate3PrunedJForEpsilon001

    gate3J0001 :
      Nat

    gate3J0001Is110 :
      gate3J0001 ≡ gate3PrunedJForEpsilon0001

    gate3J00001 :
      Nat

    gate3J00001Is1344 :
      gate3J00001 ≡ gate3PrunedJForEpsilon00001

    gate3J10Minus6 :
      Nat

    gate3J10Minus6Is200479 :
      gate3J10Minus6 ≡ gate3PrunedJForEpsilon10Minus6

    pruningPreservesCumulativeFillDistancePowerLaw :
      Set

    pruningPreservesCumulativeFillDistancePowerLawProved :
      Bool

    pruningPreservesCumulativeFillDistancePowerLawProvedIsFalse :
      pruningPreservesCumulativeFillDistancePowerLawProved ≡ false

    moscoRecoveryFromPrunedUnionDensity :
      Set

    moscoRecoveryFromPrunedUnionDensityProved :
      Bool

    moscoRecoveryFromPrunedUnionDensityProvedIsFalse :
      moscoRecoveryFromPrunedUnionDensityProved ≡ false

    nsCriticalRatio :
      Nat

    nsCriticalRatioIs0707 :
      nsCriticalRatio ≡ criticalRatioThousandths

    nsOneThirdTailK0For001 :
      Nat

    nsOneThirdTailK0For001Is7 :
      nsOneThirdTailK0For001 ≡ oneThirdTailK0ForOneHundredth

    nsOneThirdTailK0For10Minus6 :
      Nat

    nsOneThirdTailK0For10Minus6Is20 :
      nsOneThirdTailK0For10Minus6 ≡ oneThirdTailK0ForOneMillionth

    nsOneHalfTailK0For001 :
      Nat

    nsOneHalfTailK0For001Is17 :
      nsOneHalfTailK0For001 ≡ oneHalfTailK0ForOneHundredth

    nsOneHalfTailK0For10Minus6 :
      Nat

    nsOneHalfTailK0For10Minus6Is44 :
      nsOneHalfTailK0For10Minus6 ≡ oneHalfTailK0ForOneMillionth

    nsTwoThirdsTailK0For001 :
      Nat

    nsTwoThirdsTailK0For001Is127 :
      nsTwoThirdsTailK0For001 ≡ twoThirdsTailK0ForOneHundredth

    nsTwoThirdsTailK0For10Minus6 :
      Nat

    nsTwoThirdsTailK0For10Minus6Is284 :
      nsTwoThirdsTailK0For10Minus6 ≡ twoThirdsTailK0ForOneMillionth

    nsSevenTenthsTailK0For001 :
      Nat

    nsSevenTenthsTailK0For001Is912 :
      nsSevenTenthsTailK0For001 ≡ sevenTenthsTailK0ForOneHundredth

    nsSevenTenthsTailK0For10Minus6 :
      Nat

    nsSevenTenthsTailK0For10Minus6Is1824 :
      nsSevenTenthsTailK0For10Minus6 ≡ sevenTenthsTailK0ForOneMillionth

    nsSixSeventhsDiverges :
      Bool

    nsSixSeventhsDivergesIsTrue :
      nsSixSeventhsDiverges ≡ true

    nsCoherentTubeDiverges :
      Bool

    nsCoherentTubeDivergesIsTrue :
      nsCoherentTubeDiverges ≡ true

    subcriticalAbsorptionImpossibleFromLerayOnly :
      Bool

    subcriticalAbsorptionImpossibleFromLerayOnlyIsTrue :
      subcriticalAbsorptionImpossibleFromLerayOnly ≡ true

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

    ymOneLoopIncrement :
      Nat

    ymOneLoopIncrementIs01355 :
      ymOneLoopIncrement ≡ ymOneLoopIncrementTenThousandths

    ymPreferredSafeScaleK :
      Nat

    ymPreferredSafeScaleKIs67 :
      ymPreferredSafeScaleK ≡ ymPreferredSafeScale

    ymK60Shortfall :
      Nat

    ymK60ShortfallIs00308 :
      ymK60Shortfall ≡ ymK60ShortfallTenThousandths

    ymK61Tolerance :
      Nat

    ymK61ToleranceIs01048 :
      ymK61Tolerance ≡ ymK61ToleranceTenThousandths

    ymK62Tolerance :
      Nat

    ymK62ToleranceIs02403 :
      ymK62Tolerance ≡ ymK62ToleranceTenThousandths

    ymK65Tolerance :
      Nat

    ymK65ToleranceIs06469 :
      ymK65Tolerance ≡ ymK65ToleranceTenThousandths

    ymK67Tolerance :
      Nat

    ymK67ToleranceIs09180 :
      ymK67Tolerance ≡ ymK67ToleranceTenThousandths

    ymK70Tolerance :
      Nat

    ymK70ToleranceIs13247 :
      ymK70Tolerance ≡ ymK70ToleranceTenThousandths

    ymK75Tolerance :
      Nat

    ymK75ToleranceIs20024 :
      ymK75Tolerance ≡ ymK75ToleranceTenThousandths

    ymK80Tolerance :
      Nat

    ymK80ToleranceIs26802 :
      ymK80Tolerance ≡ ymK80ToleranceTenThousandths

    ymK90Tolerance :
      Nat

    ymK90ToleranceIs40357 :
      ymK90Tolerance ≡ ymK90ToleranceTenThousandths

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

    t7aBetaStar :
      Nat

    t7aBetaStarIs165556 :
      t7aBetaStar ≡ t7aBetaStarTenThousandths

    t7aSmallDepthDominates :
      Bool

    t7aSmallDepthDominatesIsTrue :
      t7aSmallDepthDominates ≡ true

    t7aCrossoverAtDepthFour :
      Bool

    t7aCrossoverAtDepthFourIsTrue :
      t7aCrossoverAtDepthFour ≡ true

    t7aDoesNotPromoteYM :
      Bool

    t7aDoesNotPromoteYMIsTrue :
      t7aDoesNotPromoteYM ≡ true

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
      List SprintTwentyTwoPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      SprintTwentyTwoPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ sprintTwentyTwoSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ sprintTwentyTwoBoundary

open ClaySprintTwentyTwoThresholdFalsificationReceipt public

canonicalClaySprintTwentyTwoThresholdFalsificationReceipt :
  ClaySprintTwentyTwoThresholdFalsificationReceipt
canonicalClaySprintTwentyTwoThresholdFalsificationReceipt =
  record
    { status =
        claySprintTwentyTwoThresholdFalsificationRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; sprintTwentyOneReceipt =
        Sprint21.canonicalClaySprintTwentyOneFrontierAuditReceipt
    ; sprintTwentyOneGate3StillFalse =
        refl
    ; sprintTwentyOneNSStillFalse =
        refl
    ; sprintTwentyOneYMStillFalse =
        refl
    ; results =
        canonicalSprintTwentyTwoResults
    ; resultsAreCanonical =
        refl
    ; resultsAreSeven =
        refl
    ; workers =
        canonicalSprintTwentyTwoWorkers
    ; workersAreCanonical =
        refl
    ; workersAreSix =
        refl
    ; openGates =
        canonicalSprintTwentyTwoOpenGates
    ; openGatesAreCanonical =
        refl
    ; openGatesAreEight =
        refl
    ; nonClaims =
        canonicalSprintTwentyTwoNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; nonClaimsAreSix =
        refl
    ; gate3AlphaNumerator =
        gate3PrunedAlphaNumerator
    ; gate3AlphaNumeratorIs92 =
        refl
    ; gate3AlphaDenominator =
        gate3PrunedAlphaDenominator
    ; gate3AlphaDenominatorIs100 =
        refl
    ; gate3PowerLawC =
        gate3PrunedCNumerator
    ; gate3PowerLawCIs07549 =
        refl
    ; gate3PowerLawCScale =
        gate3PrunedCScale
    ; gate3PowerLawCScaleIs100000 =
        refl
    ; gate3J001 =
        gate3PrunedJForEpsilon001
    ; gate3J001Is9 =
        refl
    ; gate3J0001 =
        gate3PrunedJForEpsilon0001
    ; gate3J0001Is110 =
        refl
    ; gate3J00001 =
        gate3PrunedJForEpsilon00001
    ; gate3J00001Is1344 =
        refl
    ; gate3J10Minus6 =
        gate3PrunedJForEpsilon10Minus6
    ; gate3J10Minus6Is200479 =
        refl
    ; pruningPreservesCumulativeFillDistancePowerLaw =
        ⊥
    ; pruningPreservesCumulativeFillDistancePowerLawProved =
        false
    ; pruningPreservesCumulativeFillDistancePowerLawProvedIsFalse =
        refl
    ; moscoRecoveryFromPrunedUnionDensity =
        ⊥
    ; moscoRecoveryFromPrunedUnionDensityProved =
        false
    ; moscoRecoveryFromPrunedUnionDensityProvedIsFalse =
        refl
    ; nsCriticalRatio =
        criticalRatioThousandths
    ; nsCriticalRatioIs0707 =
        refl
    ; nsOneThirdTailK0For001 =
        oneThirdTailK0ForOneHundredth
    ; nsOneThirdTailK0For001Is7 =
        refl
    ; nsOneThirdTailK0For10Minus6 =
        oneThirdTailK0ForOneMillionth
    ; nsOneThirdTailK0For10Minus6Is20 =
        refl
    ; nsOneHalfTailK0For001 =
        oneHalfTailK0ForOneHundredth
    ; nsOneHalfTailK0For001Is17 =
        refl
    ; nsOneHalfTailK0For10Minus6 =
        oneHalfTailK0ForOneMillionth
    ; nsOneHalfTailK0For10Minus6Is44 =
        refl
    ; nsTwoThirdsTailK0For001 =
        twoThirdsTailK0ForOneHundredth
    ; nsTwoThirdsTailK0For001Is127 =
        refl
    ; nsTwoThirdsTailK0For10Minus6 =
        twoThirdsTailK0ForOneMillionth
    ; nsTwoThirdsTailK0For10Minus6Is284 =
        refl
    ; nsSevenTenthsTailK0For001 =
        sevenTenthsTailK0ForOneHundredth
    ; nsSevenTenthsTailK0For001Is912 =
        refl
    ; nsSevenTenthsTailK0For10Minus6 =
        sevenTenthsTailK0ForOneMillionth
    ; nsSevenTenthsTailK0For10Minus6Is1824 =
        refl
    ; nsSixSeventhsDiverges =
        sixSeventhsDivergesRecorded
    ; nsSixSeventhsDivergesIsTrue =
        refl
    ; nsCoherentTubeDiverges =
        coherentTubeDivergesRecorded
    ; nsCoherentTubeDivergesIsTrue =
        refl
    ; subcriticalAbsorptionImpossibleFromLerayOnly =
        true
    ; subcriticalAbsorptionImpossibleFromLerayOnlyIsTrue =
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
    ; ymOneLoopIncrement =
        ymOneLoopIncrementTenThousandths
    ; ymOneLoopIncrementIs01355 =
        refl
    ; ymPreferredSafeScaleK =
        ymPreferredSafeScale
    ; ymPreferredSafeScaleKIs67 =
        refl
    ; ymK60Shortfall =
        ymK60ShortfallTenThousandths
    ; ymK60ShortfallIs00308 =
        refl
    ; ymK61Tolerance =
        ymK61ToleranceTenThousandths
    ; ymK61ToleranceIs01048 =
        refl
    ; ymK62Tolerance =
        ymK62ToleranceTenThousandths
    ; ymK62ToleranceIs02403 =
        refl
    ; ymK65Tolerance =
        ymK65ToleranceTenThousandths
    ; ymK65ToleranceIs06469 =
        refl
    ; ymK67Tolerance =
        ymK67ToleranceTenThousandths
    ; ymK67ToleranceIs09180 =
        refl
    ; ymK70Tolerance =
        ymK70ToleranceTenThousandths
    ; ymK70ToleranceIs13247 =
        refl
    ; ymK75Tolerance =
        ymK75ToleranceTenThousandths
    ; ymK75ToleranceIs20024 =
        refl
    ; ymK80Tolerance =
        ymK80ToleranceTenThousandths
    ; ymK80ToleranceIs26802 =
        refl
    ; ymK90Tolerance =
        ymK90ToleranceTenThousandths
    ; ymK90ToleranceIs40357 =
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
    ; t7aBetaStar =
        t7aBetaStarTenThousandths
    ; t7aBetaStarIs165556 =
        refl
    ; t7aSmallDepthDominates =
        true
    ; t7aSmallDepthDominatesIsTrue =
        refl
    ; t7aCrossoverAtDepthFour =
        true
    ; t7aCrossoverAtDepthFourIsTrue =
        refl
    ; t7aDoesNotPromoteYM =
        true
    ; t7aDoesNotPromoteYMIsTrue =
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
        sprintTwentyTwoPromotionImpossibleHere
    ; summary =
        sprintTwentyTwoSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        sprintTwentyTwoBoundary
    ; boundaryIsCanonical =
        refl
    }
