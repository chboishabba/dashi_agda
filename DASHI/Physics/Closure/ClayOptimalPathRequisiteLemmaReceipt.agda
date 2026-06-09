module DASHI.Physics.Closure.ClayOptimalPathRequisiteLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayHardLemmaReductionReceipt as Hard
import DASHI.Physics.Closure.ClayKernelReductionReceipt as Kernel
import DASHI.Physics.Closure.GravityVladimirovFrameReceipt as Gravity
import DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt as NSHminus
import DASHI.Physics.Closure.YMT7RademacherActivityIdentificationReceipt
  as T7Audit

------------------------------------------------------------------------
-- Clay optimal path / requisite lemma receipt.
--
-- This receipt ranks the missing theorem targets and assigns six parallel
-- workers.  It intentionally uses constructorless MissingTheoremTarget types
-- for the listed lemmas: recording a target must not inhabit the target.

data ClayOptimalPathStatus : Set where
  optimalPathRanked_requisiteLemmasRecorded_failClosed :
    ClayOptimalPathStatus

data ClayLanePriority : Set where
  priority1_YangMillsClay :
    ClayLanePriority

  priority2_NavierStokesSplit :
    ClayLanePriority

  priority3_Gate3W4GravityInfrastructure :
    ClayLanePriority

canonicalClayLanePriority : List ClayLanePriority
canonicalClayLanePriority =
  priority1_YangMillsClay
  ∷ priority2_NavierStokesSplit
  ∷ priority3_Gate3W4GravityInfrastructure
  ∷ []

data RequisiteLemma : Set where
  ym1ConnectedAnimalKPSeriesBound :
    RequisiteLemma

  ym2T7PerPolymerActivitySuppression :
    RequisiteLemma

  ym3CarrierKPToBalabanContraction :
    RequisiteLemma

  ym4PhysicalBetaBridge :
    RequisiteLemma

  ym5UniformContinuumMassGap :
    RequisiteLemma

  ym6GaugeFixedOSPositivity :
    RequisiteLemma

  ym7OSWightmanReconstruction :
    RequisiteLemma

  ym8Constructive4DYMMassGapTheorem :
    RequisiteLemma

  ymG1NonFlatSFGCCurvature :
    RequisiteLemma

  ymG2GaugeCovariantHolonomyConjugation :
    RequisiteLemma

  ymG3CovariantDerivativeSelectedBundle :
    RequisiteLemma

  ymG4HodgeStarVariationPairingIBP :
    RequisiteLemma

  ymG5BianchiAndSourcedFieldEquation :
    RequisiteLemma

  nsA1HMinusHalfObstructionTheorem :
    RequisiteLemma

  nsB1LerayBandBound :
    RequisiteLemma

  nsB2PrimeScaleBernstein :
    RequisiteLemma

  nsB3BernoulliBandH118GlobalBound :
    RequisiteLemma

  nsB4KStarDriftNonCircular :
    RequisiteLemma

  nsB5ExistenceStabilityBeforeUniqueness :
    RequisiteLemma

  nsB6CarrierToAllSmoothData :
    RequisiteLemma

  nsB7ClayNavierStokesPromotion :
    RequisiteLemma

  g3PhysicalSSPHeckeEmbeddingSpread :
    RequisiteLemma

  g3FrameUniformLowerBound :
    RequisiteLemma

  g3ContinuumTransfer :
    RequisiteLemma

  w4Candidate256PhysicalCalibration :
    RequisiteLemma

  w4WaldStressEnergySelection :
    RequisiteLemma

  grSchwarzschildWeakFieldMatch :
    RequisiteLemma

data MissingTheoremTarget : RequisiteLemma → Set where

canonicalYMClayLemmas : List RequisiteLemma
canonicalYMClayLemmas =
  ym1ConnectedAnimalKPSeriesBound
  ∷ ym2T7PerPolymerActivitySuppression
  ∷ ym3CarrierKPToBalabanContraction
  ∷ ym4PhysicalBetaBridge
  ∷ ym5UniformContinuumMassGap
  ∷ ym6GaugeFixedOSPositivity
  ∷ ym7OSWightmanReconstruction
  ∷ ym8Constructive4DYMMassGapTheorem
  ∷ []

canonicalYMGeometryLemmas : List RequisiteLemma
canonicalYMGeometryLemmas =
  ymG1NonFlatSFGCCurvature
  ∷ ymG2GaugeCovariantHolonomyConjugation
  ∷ ymG3CovariantDerivativeSelectedBundle
  ∷ ymG4HodgeStarVariationPairingIBP
  ∷ ymG5BianchiAndSourcedFieldEquation
  ∷ []

canonicalNSLemmas : List RequisiteLemma
canonicalNSLemmas =
  nsA1HMinusHalfObstructionTheorem
  ∷ nsB1LerayBandBound
  ∷ nsB2PrimeScaleBernstein
  ∷ nsB3BernoulliBandH118GlobalBound
  ∷ nsB4KStarDriftNonCircular
  ∷ nsB5ExistenceStabilityBeforeUniqueness
  ∷ nsB6CarrierToAllSmoothData
  ∷ nsB7ClayNavierStokesPromotion
  ∷ []

canonicalGate3W4GRLemmas : List RequisiteLemma
canonicalGate3W4GRLemmas =
  g3PhysicalSSPHeckeEmbeddingSpread
  ∷ g3FrameUniformLowerBound
  ∷ g3ContinuumTransfer
  ∷ w4Candidate256PhysicalCalibration
  ∷ w4WaldStressEnergySelection
  ∷ grSchwarzschildWeakFieldMatch
  ∷ []

data ParallelWorker : Set where
  worker1YMActivity :
    ParallelWorker

  worker2YMBalaban :
    ParallelWorker

  worker3YMOSAndGeometry :
    ParallelWorker

  worker4NavierStokes :
    ParallelWorker

  worker5Gate3W4Gravity :
    ParallelWorker

  worker6Governance :
    ParallelWorker

canonicalParallelWorkers : List ParallelWorker
canonicalParallelWorkers =
  worker1YMActivity
  ∷ worker2YMBalaban
  ∷ worker3YMOSAndGeometry
  ∷ worker4NavierStokes
  ∷ worker5Gate3W4Gravity
  ∷ worker6Governance
  ∷ []

data WorkerAssignment : Set where
  w1ConnectedAnimalAndT7Activity :
    WorkerAssignment

  w2BalabanBetaBridgeAndUniformGap :
    WorkerAssignment

  w3OSWightmanAndYMFieldGeometry :
    WorkerAssignment

  w4NSObstructionAndH118Route :
    WorkerAssignment

  w5Gate3W4GRInfrastructure :
    WorkerAssignment

  w6GovernanceKillTestsAndSourceMap :
    WorkerAssignment

canonicalWorkerAssignments : List WorkerAssignment
canonicalWorkerAssignments =
  w1ConnectedAnimalAndT7Activity
  ∷ w2BalabanBetaBridgeAndUniformGap
  ∷ w3OSWightmanAndYMFieldGeometry
  ∷ w4NSObstructionAndH118Route
  ∷ w5Gate3W4GRInfrastructure
  ∷ w6GovernanceKillTestsAndSourceMap
  ∷ []

data OptimalPathPromotion : Set where

optimalPathPromotionImpossibleHere :
  OptimalPathPromotion →
  ⊥
optimalPathPromotionImpossibleHere ()

ymWorkOrderText : String
ymWorkOrderText =
  "YM first: connected-animal KP bound beta* ~= 9.593637, T7A per-polymer activity suppression as optional improvement, KP-to-Balaban, beta_phys ~= 6 to beta_eff above the strict Balaban seed margin, recording 9.593637, 10.13086, and exact beta*c_min-a>log(2p) separately, uniform continuum mass gap, gauge-fixed OS positivity, OS/Wightman, then Clay YM promotion theorem."

nsWorkOrderText : String
nsWorkOrderText =
  "NS second: publish H^{-1/2} obstruction as Path A; Path B needs H^{11/8} Bernoulli bound, non-circular K* drift, existence/stability before uniqueness, and carrier-to-all-smooth-data extension."

gate3W4WorkOrderText : String
gate3W4WorkOrderText =
  "Gate3/W4/gravity third: physical SSP spread, frame lower bounds, Mosco/no-pollution/mass-shell transfer, Candidate256 physical calibration, Wald stress-energy authority, and Schwarzschild weak-field match."

receiptBoundaryText : String
receiptBoundaryText =
  "Every listed lemma is a missing theorem target unless consumed from an existing exact receipt.  This receipt assigns workers and ranks obligations only; it proves no Clay, Gate3, gravity, W4, Schwarzschild, YM, NS, or terminal promotion."

connectedAnimalThresholdHundredths : Nat
connectedAnimalThresholdHundredths =
  959

connectedAnimalGapFromPhysicalHundredths : Nat
connectedAnimalGapFromPhysicalHundredths =
  359

directT7ThresholdHundredths : Nat
directT7ThresholdHundredths =
  1656

directT7GapFromPhysicalHundredths : Nat
directT7GapFromPhysicalHundredths =
  1056

physicalBetaHundredths : Nat
physicalBetaHundredths =
  600

record ClayOptimalPathRequisiteLemmaReceipt : Setω where
  field
    status :
      ClayOptimalPathStatus

    statusIsCanonical :
      status ≡ optimalPathRanked_requisiteLemmasRecorded_failClosed

    kernelReceipt :
      Kernel.ClayKernelReductionReceipt

    kernelYMStillFalse :
      Kernel.ymPromotion kernelReceipt ≡ false

    kernelNSStillFalse :
      Kernel.nsPromotion kernelReceipt ≡ false

    kernelGate3StillFalse :
      Kernel.gate3Promotion kernelReceipt ≡ false

    hardReceipt :
      Hard.ClayHardLemmaReductionReceipt

    hardNoYM :
      Hard.clayYangMillsPromoted hardReceipt ≡ false

    hardNoNS :
      Hard.clayNavierStokesPromoted hardReceipt ≡ false

    hardNoGravity :
      Hard.gravityPredictionPromoted hardReceipt ≡ false

    hardNoW4 :
      Hard.w4PhysicalMassCalibrated hardReceipt ≡ false

    t7AuditReceipt :
      T7Audit.YMT7RademacherActivityIdentificationReceipt

    t7DirectKPSumComputed :
      T7Audit.ymT7DirectKPSumThresholdComputed t7AuditReceipt ≡ true

    t7BalabanStillOpen :
      T7Audit.balabanBridgeProved t7AuditReceipt ≡ false

    t7OSWightmanStillOpen :
      T7Audit.osWightmanReconstructionProved t7AuditReceipt ≡ false

    t7YMStillFalse :
      T7Audit.clayYangMillsPromoted t7AuditReceipt ≡ false

    nsHminusReceipt :
      NSHminus.NSHminus1Over2ObstructionReceipt

    nsHminusDiverges :
      NSHminus.ratioDivergesAsNuToZero nsHminusReceipt ≡ true

    nsHminusNoClay :
      NSHminus.clayNavierStokesPromoted nsHminusReceipt ≡ false

    gravityReceipt :
      Gravity.GravityVladimirovFrameReceipt

    gravitySSPStillOpen :
      Gravity.sspEmbeddingGravity3DObligation gravityReceipt ≡ false

    gravityW4StillOpen :
      Gravity.w4PhysicalMassCalibrationSupplied gravityReceipt ≡ false

    gravitySchwarzschildStillOpen :
      Gravity.schwarzschildMetricMatchProved gravityReceipt ≡ false

    gravityStillFalse :
      Gravity.gravityPredictionPromoted gravityReceipt ≡ false

    priorities :
      List ClayLanePriority

    prioritiesAreCanonical :
      priorities ≡ canonicalClayLanePriority

    ymClayLemmas :
      List RequisiteLemma

    ymClayLemmasAreCanonical :
      ymClayLemmas ≡ canonicalYMClayLemmas

    ymGeometryLemmas :
      List RequisiteLemma

    ymGeometryLemmasAreCanonical :
      ymGeometryLemmas ≡ canonicalYMGeometryLemmas

    nsLemmas :
      List RequisiteLemma

    nsLemmasAreCanonical :
      nsLemmas ≡ canonicalNSLemmas

    gate3W4GRLemmas :
      List RequisiteLemma

    gate3W4GRLemmasAreCanonical :
      gate3W4GRLemmas ≡ canonicalGate3W4GRLemmas

    workers :
      List ParallelWorker

    workersAreCanonical :
      workers ≡ canonicalParallelWorkers

    workerAssignments :
      List WorkerAssignment

    workerAssignmentsAreCanonical :
      workerAssignments ≡ canonicalWorkerAssignments

    ymConnectedAnimalKPSumLemma :
      Set

    ymConnectedAnimalKPSumLemmaIsMissingTarget :
      ymConnectedAnimalKPSumLemma
      ≡
      MissingTheoremTarget ym1ConnectedAnimalKPSeriesBound

    ymT7PerPolymerActivitySuppressionLemma :
      Set

    ymT7PerPolymerActivitySuppressionLemmaIsMissingTarget :
      ymT7PerPolymerActivitySuppressionLemma
      ≡
      MissingTheoremTarget ym2T7PerPolymerActivitySuppression

    ymPhysicalBetaBridge :
      Set

    ymPhysicalBetaBridgeIsMissingTarget :
      ymPhysicalBetaBridge ≡ MissingTheoremTarget ym4PhysicalBetaBridge

    nsHMinusHalfObstruction :
      Set

    nsHMinusHalfObstructionIsMissingTarget :
      nsHMinusHalfObstruction
      ≡
      MissingTheoremTarget nsA1HMinusHalfObstructionTheorem

    nsBernoulliBandH118GlobalBound :
      Set

    nsBernoulliBandH118GlobalBoundIsMissingTarget :
      nsBernoulliBandH118GlobalBound
      ≡
      MissingTheoremTarget nsB3BernoulliBandH118GlobalBound

    nsKStarDriftNonCircular :
      Set

    nsKStarDriftNonCircularIsMissingTarget :
      nsKStarDriftNonCircular
      ≡
      MissingTheoremTarget nsB4KStarDriftNonCircular

    gate3PhysicalSSPEmbeddingSpread :
      Set

    gate3PhysicalSSPEmbeddingSpreadIsMissingTarget :
      gate3PhysicalSSPEmbeddingSpread
      ≡
      MissingTheoremTarget g3PhysicalSSPHeckeEmbeddingSpread

    w4Candidate256PhysicalCalibrationLemma :
      Set

    w4Candidate256PhysicalCalibrationLemmaIsMissingTarget :
      w4Candidate256PhysicalCalibrationLemma
      ≡
      MissingTheoremTarget w4Candidate256PhysicalCalibration

    connectedAnimalThreshold :
      Nat

    connectedAnimalThresholdIs959 :
      connectedAnimalThreshold ≡ connectedAnimalThresholdHundredths

    connectedAnimalGapFromPhysical :
      Nat

    connectedAnimalGapFromPhysicalIs359 :
      connectedAnimalGapFromPhysical
      ≡
      connectedAnimalGapFromPhysicalHundredths

    directT7Threshold :
      Nat

    directT7ThresholdIs1656 :
      directT7Threshold ≡ directT7ThresholdHundredths

    directT7GapFromPhysical :
      Nat

    directT7GapFromPhysicalIs1056 :
      directT7GapFromPhysical ≡ directT7GapFromPhysicalHundredths

    physicalBeta :
      Nat

    physicalBetaIs600 :
      physicalBeta ≡ physicalBetaHundredths

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gravityPredictionPromoted :
      Bool

    gravityPredictionPromotedIsFalse :
      gravityPredictionPromoted ≡ false

    gate3SpectralGapProved :
      Bool

    gate3SpectralGapProvedIsFalse :
      gate3SpectralGapProved ≡ false

    w4PhysicalMassCalibrated :
      Bool

    w4PhysicalMassCalibratedIsFalse :
      w4PhysicalMassCalibrated ≡ false

    schwarzschildWeakFieldMatch :
      Bool

    schwarzschildWeakFieldMatchIsFalse :
      schwarzschildWeakFieldMatch ≡ false

    promotions :
      List OptimalPathPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      OptimalPathPromotion →
      ⊥

    ymText :
      String

    ymTextIsCanonical :
      ymText ≡ ymWorkOrderText

    nsText :
      String

    nsTextIsCanonical :
      nsText ≡ nsWorkOrderText

    gate3W4Text :
      String

    gate3W4TextIsCanonical :
      gate3W4Text ≡ gate3W4WorkOrderText

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

open ClayOptimalPathRequisiteLemmaReceipt public

canonicalClayOptimalPathRequisiteLemmaReceipt :
  ClayOptimalPathRequisiteLemmaReceipt
canonicalClayOptimalPathRequisiteLemmaReceipt =
  record
    { status =
        optimalPathRanked_requisiteLemmasRecorded_failClosed
    ; statusIsCanonical =
        refl
    ; kernelReceipt =
        Kernel.canonicalClayKernelReductionReceipt
    ; kernelYMStillFalse =
        refl
    ; kernelNSStillFalse =
        refl
    ; kernelGate3StillFalse =
        refl
    ; hardReceipt =
        Hard.canonicalClayHardLemmaReductionReceipt
    ; hardNoYM =
        refl
    ; hardNoNS =
        refl
    ; hardNoGravity =
        refl
    ; hardNoW4 =
        refl
    ; t7AuditReceipt =
        T7Audit.canonicalYMT7RademacherActivityIdentificationReceipt
    ; t7DirectKPSumComputed =
        refl
    ; t7BalabanStillOpen =
        refl
    ; t7OSWightmanStillOpen =
        refl
    ; t7YMStillFalse =
        refl
    ; nsHminusReceipt =
        NSHminus.canonicalNSHminus1Over2ObstructionReceipt
    ; nsHminusDiverges =
        refl
    ; nsHminusNoClay =
        refl
    ; gravityReceipt =
        Gravity.canonicalGravityVladimirovFrameReceipt
    ; gravitySSPStillOpen =
        refl
    ; gravityW4StillOpen =
        refl
    ; gravitySchwarzschildStillOpen =
        refl
    ; gravityStillFalse =
        refl
    ; priorities =
        canonicalClayLanePriority
    ; prioritiesAreCanonical =
        refl
    ; ymClayLemmas =
        canonicalYMClayLemmas
    ; ymClayLemmasAreCanonical =
        refl
    ; ymGeometryLemmas =
        canonicalYMGeometryLemmas
    ; ymGeometryLemmasAreCanonical =
        refl
    ; nsLemmas =
        canonicalNSLemmas
    ; nsLemmasAreCanonical =
        refl
    ; gate3W4GRLemmas =
        canonicalGate3W4GRLemmas
    ; gate3W4GRLemmasAreCanonical =
        refl
    ; workers =
        canonicalParallelWorkers
    ; workersAreCanonical =
        refl
    ; workerAssignments =
        canonicalWorkerAssignments
    ; workerAssignmentsAreCanonical =
        refl
    ; ymConnectedAnimalKPSumLemma =
        MissingTheoremTarget ym1ConnectedAnimalKPSeriesBound
    ; ymConnectedAnimalKPSumLemmaIsMissingTarget =
        refl
    ; ymT7PerPolymerActivitySuppressionLemma =
        MissingTheoremTarget ym2T7PerPolymerActivitySuppression
    ; ymT7PerPolymerActivitySuppressionLemmaIsMissingTarget =
        refl
    ; ymPhysicalBetaBridge =
        MissingTheoremTarget ym4PhysicalBetaBridge
    ; ymPhysicalBetaBridgeIsMissingTarget =
        refl
    ; nsHMinusHalfObstruction =
        MissingTheoremTarget nsA1HMinusHalfObstructionTheorem
    ; nsHMinusHalfObstructionIsMissingTarget =
        refl
    ; nsBernoulliBandH118GlobalBound =
        MissingTheoremTarget nsB3BernoulliBandH118GlobalBound
    ; nsBernoulliBandH118GlobalBoundIsMissingTarget =
        refl
    ; nsKStarDriftNonCircular =
        MissingTheoremTarget nsB4KStarDriftNonCircular
    ; nsKStarDriftNonCircularIsMissingTarget =
        refl
    ; gate3PhysicalSSPEmbeddingSpread =
        MissingTheoremTarget g3PhysicalSSPHeckeEmbeddingSpread
    ; gate3PhysicalSSPEmbeddingSpreadIsMissingTarget =
        refl
    ; w4Candidate256PhysicalCalibrationLemma =
        MissingTheoremTarget w4Candidate256PhysicalCalibration
    ; w4Candidate256PhysicalCalibrationLemmaIsMissingTarget =
        refl
    ; connectedAnimalThreshold =
        connectedAnimalThresholdHundredths
    ; connectedAnimalThresholdIs959 =
        refl
    ; connectedAnimalGapFromPhysical =
        connectedAnimalGapFromPhysicalHundredths
    ; connectedAnimalGapFromPhysicalIs359 =
        refl
    ; directT7Threshold =
        directT7ThresholdHundredths
    ; directT7ThresholdIs1656 =
        refl
    ; directT7GapFromPhysical =
        directT7GapFromPhysicalHundredths
    ; directT7GapFromPhysicalIs1056 =
        refl
    ; physicalBeta =
        physicalBetaHundredths
    ; physicalBetaIs600 =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gravityPredictionPromoted =
        false
    ; gravityPredictionPromotedIsFalse =
        refl
    ; gate3SpectralGapProved =
        false
    ; gate3SpectralGapProvedIsFalse =
        refl
    ; w4PhysicalMassCalibrated =
        false
    ; w4PhysicalMassCalibratedIsFalse =
        refl
    ; schwarzschildWeakFieldMatch =
        false
    ; schwarzschildWeakFieldMatchIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        optimalPathPromotionImpossibleHere
    ; ymText =
        ymWorkOrderText
    ; ymTextIsCanonical =
        refl
    ; nsText =
        nsWorkOrderText
    ; nsTextIsCanonical =
        refl
    ; gate3W4Text =
        gate3W4WorkOrderText
    ; gate3W4TextIsCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

optimalPathKeepsYMFalse :
  clayYangMillsPromoted canonicalClayOptimalPathRequisiteLemmaReceipt
  ≡
  false
optimalPathKeepsYMFalse =
  refl

optimalPathKeepsNSFalse :
  clayNavierStokesPromoted canonicalClayOptimalPathRequisiteLemmaReceipt
  ≡
  false
optimalPathKeepsNSFalse =
  refl

optimalPathKeepsGravityFalse :
  gravityPredictionPromoted canonicalClayOptimalPathRequisiteLemmaReceipt
  ≡
  false
optimalPathKeepsGravityFalse =
  refl
