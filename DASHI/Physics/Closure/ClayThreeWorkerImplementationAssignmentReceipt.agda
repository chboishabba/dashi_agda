module DASHI.Physics.Closure.ClayThreeWorkerImplementationAssignmentReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PhysicalSSPHeckeModelClosureReceipt
  as Gate3
import DASHI.Physics.Closure.NSHighLowFluxControlAuditReceipt
  as NS
import DASHI.Physics.Closure.YMFortyTwoStepBalabanTargetReceipt
  as YM

------------------------------------------------------------------------
-- Three-worker implementation assignment.
--
-- This receipt assigns one implementation worker to each shortest live
-- bridge: Gate3 support, NS Clay-facing audit, and YM Balaban target.
-- It records ownership only; no worker assignment inhabits a theorem.

data ClayWorkerAssignmentStatus : Set where
  clayThreeWorkerImplementationAssignmentRecorded_noPromotion :
    ClayWorkerAssignmentStatus

data ClayImplementationWorker : Set where
  w1Gate3SSPHeckeIdentification :
    ClayImplementationWorker

  w2NSHighLowFluxAudit :
    ClayImplementationWorker

  w3YMFortyTwoStepBalaban :
    ClayImplementationWorker

canonicalClayImplementationWorkers :
  List ClayImplementationWorker
canonicalClayImplementationWorkers =
  w1Gate3SSPHeckeIdentification
  ∷ w2NSHighLowFluxAudit
  ∷ w3YMFortyTwoStepBalaban
  ∷ []

data ClayImplementationTask : Set where
  implementSSPCarrierEqualsHeckeModel :
    ClayImplementationTask

  implementHighLowFluxControlAuditOrCounterfamily :
    ClayImplementationTask

  implementFortyTwoStepBalabanUniformityTarget :
    ClayImplementationTask

canonicalClayImplementationTasks :
  List ClayImplementationTask
canonicalClayImplementationTasks =
  implementSSPCarrierEqualsHeckeModel
  ∷ implementHighLowFluxControlAuditOrCounterfamily
  ∷ implementFortyTwoStepBalabanUniformityTarget
  ∷ []

data ClayWorkerAssignmentNonClaim : Set where
  assignmentIsNotProof :
    ClayWorkerAssignmentNonClaim

  oneWorkerPerBridgeIsNotBridgeClosure :
    ClayWorkerAssignmentNonClaim

  implementationAttemptMayReturnCounterexample :
    ClayWorkerAssignmentNonClaim

  noClayPromotion :
    ClayWorkerAssignmentNonClaim

canonicalClayWorkerAssignmentNonClaims :
  List ClayWorkerAssignmentNonClaim
canonicalClayWorkerAssignmentNonClaims =
  assignmentIsNotProof
  ∷ oneWorkerPerBridgeIsNotBridgeClosure
  ∷ implementationAttemptMayReturnCounterexample
  ∷ noClayPromotion
  ∷ []

data ClayThreeWorkerAssignmentPromotion : Set where

clayThreeWorkerAssignmentPromotionImpossibleHere :
  ClayThreeWorkerAssignmentPromotion →
  ⊥
clayThreeWorkerAssignmentPromotionImpossibleHere ()

workerCount : Nat
workerCount =
  3

gate3AssignmentText : String
gate3AssignmentText =
  "W1 Gate3: implement or kill SSPCarrierEqualsHeckeModel. Success routes HeckeModelSpreadBound and S3DAtHeckeSpreadBelowOne into UniformFrameLowerBound; failure leaves Gate3 support blocked."

nsAssignmentText : String
nsAssignmentText =
  "W2 NS: implement the HighLow flux audit. Prove the K^{-1/2} suppression without hidden L_infinity/Serrin/BKM/H118 input, or produce a Leray-energy-bounded HighLow counterfamily."

ymAssignmentText : String
ymAssignmentText =
  "W3 YM: implement the 42-step Balaban target. Prove uniform nonperturbative block-spin control with summable leakage toward beta_eff>=13.7, or return the exact failed step."

assignmentBoundaryText : String
assignmentBoundaryText =
  "This receipt assigns one worker to each live implementation bridge. It does not prove the bridges, close Gate3, prove NS or YM Clay, or flip any promotion flag."

record ClayThreeWorkerImplementationAssignmentReceipt : Setω where
  field
    status :
      ClayWorkerAssignmentStatus

    statusIsCanonical :
      status ≡ clayThreeWorkerImplementationAssignmentRecorded_noPromotion

    gate3Receipt :
      Gate3.PhysicalSSPHeckeModelClosureReceipt

    gate3BridgeStillOpen :
      Gate3.sspCarrierEqualsHeckeModelProved gate3Receipt ≡ false

    gate3StillFalse :
      Gate3.gate3Closed gate3Receipt ≡ false

    nsReceipt :
      NS.NSHighLowFluxControlAuditReceipt

    nsHighLowStillRejected :
      NS.highLowBoundAccepted nsReceipt ≡ false

    nsStillFalse :
      NS.clayNavierStokesPromoted nsReceipt ≡ false

    ymReceipt :
      YM.YMFortyTwoStepBalabanTargetReceipt

    ymBalabanStillOpen :
      YM.balabanTransferProved ymReceipt ≡ false

    ymStillFalse :
      YM.clayYangMillsPromoted ymReceipt ≡ false

    workers :
      List ClayImplementationWorker

    workersAreCanonical :
      workers ≡ canonicalClayImplementationWorkers

    tasks :
      List ClayImplementationTask

    tasksAreCanonical :
      tasks ≡ canonicalClayImplementationTasks

    nonClaims :
      List ClayWorkerAssignmentNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalClayWorkerAssignmentNonClaims

    workerCountRecorded :
      Nat

    workerCountIs3 :
      workerCountRecorded ≡ workerCount

    exactlyOneWorkerPerBridge :
      Bool

    exactlyOneWorkerPerBridgeIsTrue :
      exactlyOneWorkerPerBridge ≡ true

    gate3WorkerAssigned :
      Bool

    gate3WorkerAssignedIsTrue :
      gate3WorkerAssigned ≡ true

    nsWorkerAssigned :
      Bool

    nsWorkerAssignedIsTrue :
      nsWorkerAssigned ≡ true

    ymWorkerAssigned :
      Bool

    ymWorkerAssignedIsTrue :
      ymWorkerAssigned ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    promotions :
      List ClayThreeWorkerAssignmentPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ClayThreeWorkerAssignmentPromotion →
      ⊥

    gate3Assignment :
      String

    gate3AssignmentIsCanonical :
      gate3Assignment ≡ gate3AssignmentText

    nsAssignment :
      String

    nsAssignmentIsCanonical :
      nsAssignment ≡ nsAssignmentText

    ymAssignment :
      String

    ymAssignmentIsCanonical :
      ymAssignment ≡ ymAssignmentText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ assignmentBoundaryText

open ClayThreeWorkerImplementationAssignmentReceipt public

canonicalClayThreeWorkerImplementationAssignmentReceipt :
  ClayThreeWorkerImplementationAssignmentReceipt
canonicalClayThreeWorkerImplementationAssignmentReceipt =
  record
    { status =
        clayThreeWorkerImplementationAssignmentRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; gate3Receipt =
        Gate3.canonicalPhysicalSSPHeckeModelClosureReceipt
    ; gate3BridgeStillOpen =
        refl
    ; gate3StillFalse =
        refl
    ; nsReceipt =
        NS.canonicalNSHighLowFluxControlAuditReceipt
    ; nsHighLowStillRejected =
        refl
    ; nsStillFalse =
        refl
    ; ymReceipt =
        YM.canonicalYMFortyTwoStepBalabanTargetReceipt
    ; ymBalabanStillOpen =
        refl
    ; ymStillFalse =
        refl
    ; workers =
        canonicalClayImplementationWorkers
    ; workersAreCanonical =
        refl
    ; tasks =
        canonicalClayImplementationTasks
    ; tasksAreCanonical =
        refl
    ; nonClaims =
        canonicalClayWorkerAssignmentNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; workerCountRecorded =
        workerCount
    ; workerCountIs3 =
        refl
    ; exactlyOneWorkerPerBridge =
        true
    ; exactlyOneWorkerPerBridgeIsTrue =
        refl
    ; gate3WorkerAssigned =
        true
    ; gate3WorkerAssignedIsTrue =
        refl
    ; nsWorkerAssigned =
        true
    ; nsWorkerAssignedIsTrue =
        refl
    ; ymWorkerAssigned =
        true
    ; ymWorkerAssignedIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        clayThreeWorkerAssignmentPromotionImpossibleHere
    ; gate3Assignment =
        gate3AssignmentText
    ; gate3AssignmentIsCanonical =
        refl
    ; nsAssignment =
        nsAssignmentText
    ; nsAssignmentIsCanonical =
        refl
    ; ymAssignment =
        ymAssignmentText
    ; ymAssignmentIsCanonical =
        refl
    ; boundary =
        assignmentBoundaryText
    ; boundaryIsCanonical =
        refl
    }

canonicalThreeWorkerAssignmentNoClayYM :
  clayYangMillsPromoted canonicalClayThreeWorkerImplementationAssignmentReceipt
  ≡
  false
canonicalThreeWorkerAssignmentNoClayYM =
  refl

canonicalThreeWorkerAssignmentNoClayNS :
  clayNavierStokesPromoted
    canonicalClayThreeWorkerImplementationAssignmentReceipt
  ≡
  false
canonicalThreeWorkerAssignmentNoClayNS =
  refl
