module DASHI.Physics.Closure.NSNonCircularKStarDriftBoundTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSAdjacentShellLeakageBoundReceipt as Leak
import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as Danger
import DASHI.Physics.Closure.NSDangerShellMaxPrincipleConditionalProofReceipt
  as Conditional
import DASHI.Physics.Closure.NSNonCircularObstructionReceipt as Obstruction
import DASHI.Physics.Closure.NSNegativeSobolevDangerShellReceipt as NegSob
import DASHI.Physics.Closure.NSThetaTailToBKMBridgeReceipt as TailBKM
import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt as Full
import DASHI.Physics.Closure.ParaproductDecompositionReceipt as Paraproduct

------------------------------------------------------------------------
-- Non-circular K-star drift bound target.
--
-- This receipt records the exact next theorem target after the high-high
-- obstruction receipt.  At the danger shell K*(t), prove a strict tail
-- absorption inequality
--
--   Flux_{>K*(t)} <= (1-c) Diss_{>K*(t)}
--
-- equivalently theta_{K*(t)} <= 1-c, without assuming H^{1/2}, Serrin,
-- BKM, or stronger regularity.  The admissible replacement is the
-- H^{-1/2} nonlinear-defect estimate recorded in
-- `NSNegativeSobolevDangerShellReceipt`.  It is a target/obligation receipt
-- only: the non-circular high-high estimate, K*(t) drift containment, edge
-- influx, theta preservation, and tail-to-continuation route remain open here.

data NSNonCircularKStarDriftBoundTargetStatus : Set where
  nonCircularKStarDriftBoundExactTargetRecorded :
    NSNonCircularKStarDriftBoundTargetStatus

data NonCircularKStarTheoremTarget : Set where
  proveFluxTailStrictlyAbsorbedAtDangerShell :
    NonCircularKStarTheoremTarget

  proveThetaPreservationAtDangerShellEquivalently :
    NonCircularKStarTheoremTarget

  proveKStarDriftContainmentByViscousScale :
    NonCircularKStarTheoremTarget

canonicalNonCircularKStarTheoremTargets :
  List NonCircularKStarTheoremTarget
canonicalNonCircularKStarTheoremTargets =
  proveFluxTailStrictlyAbsorbedAtDangerShell
  ∷ proveThetaPreservationAtDangerShellEquivalently
  ∷ proveKStarDriftContainmentByViscousScale
  ∷ []

data HighHighObstructionClause : Set where
  lowHighIsNotCoreObstruction :
    HighHighObstructionClause

  highHighParaproductIsLoadBearing :
    HighHighObstructionClause

  serrinAssumptionMakesProofCircular :
    HighHighObstructionClause

  bkmAssumptionMakesProofCircular :
    HighHighObstructionClause

  hHalfOrStrongerRegularityAssumptionMakesProofCircular :
    HighHighObstructionClause

  computedLowHighRatioBelowThetaBarrier :
    HighHighObstructionClause

  computedHighHighTermCrossesThetaBarrier :
    HighHighObstructionClause

  highHighNeedsHMinusHalfDefectControl :
    HighHighObstructionClause

canonicalHighHighObstructionClauses :
  List HighHighObstructionClause
canonicalHighHighObstructionClauses =
  lowHighIsNotCoreObstruction
  ∷ highHighParaproductIsLoadBearing
  ∷ serrinAssumptionMakesProofCircular
  ∷ bkmAssumptionMakesProofCircular
  ∷ hHalfOrStrongerRegularityAssumptionMakesProofCircular
  ∷ computedLowHighRatioBelowThetaBarrier
  ∷ computedHighHighTermCrossesThetaBarrier
  ∷ highHighNeedsHMinusHalfDefectControl
  ∷ []

data NonCircularKStarOpenObligation : Set where
  nonCircularHighHighControl :
    NonCircularKStarOpenObligation

  kStarTLeqKStarNuDriftContainment :
    NonCircularKStarOpenObligation

  edgeInfluxBoundAtDangerShell :
    NonCircularKStarOpenObligation

  thetaLessThanOnePreservation :
    NonCircularKStarOpenObligation

  tailToContinuationAfterPriorObligationsOnly :
    NonCircularKStarOpenObligation

  intrinsicHighHighEstimateReplacingHOneHalfInput :
    NonCircularKStarOpenObligation

  hMinusHalfNonlinearDefectEstimateAtDangerShell :
    NonCircularKStarOpenObligation

canonicalNonCircularKStarOpenObligations :
  List NonCircularKStarOpenObligation
canonicalNonCircularKStarOpenObligations =
  nonCircularHighHighControl
  ∷ kStarTLeqKStarNuDriftContainment
  ∷ edgeInfluxBoundAtDangerShell
  ∷ thetaLessThanOnePreservation
  ∷ tailToContinuationAfterPriorObligationsOnly
  ∷ intrinsicHighHighEstimateReplacingHOneHalfInput
  ∷ hMinusHalfNonlinearDefectEstimateAtDangerShell
  ∷ []

data ForbiddenCircularInput : Set where
  noHOneHalfInput :
    ForbiddenCircularInput

  noSerrinInput :
    ForbiddenCircularInput

  noBKMInput :
    ForbiddenCircularInput

  noStrongerRegularityInput :
    ForbiddenCircularInput

canonicalForbiddenCircularInputs :
  List ForbiddenCircularInput
canonicalForbiddenCircularInputs =
  noHOneHalfInput
  ∷ noSerrinInput
  ∷ noBKMInput
  ∷ noStrongerRegularityInput
  ∷ []

data TailContinuationOrder : Set where
  firstFixedKIdentity :
    TailContinuationOrder

  thenAdjacentEdgeInfluxAccounting :
    TailContinuationOrder

  thenNonCircularHighHighControl :
    TailContinuationOrder

  thenKStarDriftContainment :
    TailContinuationOrder

  thenThetaPreservation :
    TailContinuationOrder

  thenTailToBKMSerrinContinuation :
    TailContinuationOrder

canonicalTailContinuationOrder :
  List TailContinuationOrder
canonicalTailContinuationOrder =
  firstFixedKIdentity
  ∷ thenAdjacentEdgeInfluxAccounting
  ∷ thenNonCircularHighHighControl
  ∷ thenKStarDriftContainment
  ∷ thenThetaPreservation
  ∷ thenTailToBKMSerrinContinuation
  ∷ []

data NSNonCircularKStarPromotion : Set where

nsNonCircularKStarPromotionImpossibleHere :
  NSNonCircularKStarPromotion →
  ⊥
nsNonCircularKStarPromotionImpossibleHere ()

nonCircularKStarTargetFormula :
  String
nonCircularKStarTargetFormula =
  "NonCircularKStarDriftBound target: at the danger shell K*(t), prove Flux_{>K*(t)} <= (1-c) Diss_{>K*(t)} for c>0, equivalently theta_{K*(t)} <= 1-c, without assuming H^{1/2}, Serrin, BKM, or stronger regularity."

highHighObstructionStatement :
  String
highHighObstructionStatement =
  "Low-high leakage is not the core obstruction: computed diagnostics keep the LH paraproduct ratio below theta=1.  The load-bearing obstruction is the high-high paraproduct, which crosses/exceeds the barrier in small-nu, large-shell danger regimes.  The admissible replacement is an H^{-1/2} nonlinear-defect estimate for P_{>K*}(u.grad u); importing Serrin, BKM, H^{1/2} velocity control, or stronger regularity makes the drift-bound proof circular."

openObligationStatement :
  String
openObligationStatement =
  "Open order: prove the H^{-1/2} nonlinear-defect bound replacing H^{1/2} velocity regularity, prove K*(t)<=K*(nu) drift containment, edge influx bound, theta preservation, and only then use the tail-to-continuation bridge."

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "This receipt records the exact theorem target only.  It does not prove NonCircularKStarDriftBound, theta preservation, BKM/Serrin continuation, global regularity, Clay Navier-Stokes, or terminal promotion."

record NSNonCircularKStarDriftBoundTargetReceipt : Setω where
  field
    status :
      NSNonCircularKStarDriftBoundTargetStatus

    statusIsCanonical :
      status ≡ nonCircularKStarDriftBoundExactTargetRecorded

    obstructionReceipt :
      Obstruction.NSNonCircularObstructionReceipt

    obstructionHighHighControlOpen :
      Obstruction.highHighControlProvedHere obstructionReceipt ≡ false

    obstructionNoSerrinOrBKM :
      Obstruction.serrinOrBKMAssumedByAllowedProof obstructionReceipt ≡ false

    obstructionNoClay :
      Obstruction.clayNavierStokesPromoted obstructionReceipt ≡ false

    negativeSobolevReceipt :
      NegSob.NSNegativeSobolevDangerShellReceipt zero

    negativeSobolevTargetRecorded :
      NegSob.nonlinearDefectSpaceTargetRecorded negativeSobolevReceipt
      ≡
      true

    negativeSobolevDualPairingRecorded :
      NegSob.dualPairingRecorded negativeSobolevReceipt ≡ true

    negativeSobolevDefectBoundOpen :
      NegSob.highHighDefectBoundProvedHere negativeSobolevReceipt
      ≡
      false

    negativeSobolevNoHOneHalfShortcut :
      NegSob.hOneHalfVelocityRegularityAssumed negativeSobolevReceipt
      ≡
      false

    negativeSobolevNoClay :
      NegSob.clayNavierStokesPromoted negativeSobolevReceipt ≡ false

    tailToBKMReceipt :
      TailBKM.NSThetaTailToBKMBridgeReceipt zero

    tailToBKMKStarDriftOpen :
      TailBKM.KStarDriftBoundProvedHere tailToBKMReceipt ≡ false

    tailToBKMCriterionOpen :
      TailBKM.bkmCriterionDischarged tailToBKMReceipt ≡ false

    tailToBKMNoClay :
      TailBKM.clayNavierStokesPromoted tailToBKMReceipt ≡ false

    dangerShellReceipt :
      Danger.NSDangerShellMaximumPrincipleReceipt

    dangerShellTargetOpen :
      Danger.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false

    dangerShellEdgeLeakageOpen :
      Danger.edgeLeakageBoundOpen dangerShellReceipt ≡ true

    dangerShellNoClay :
      Danger.clayNavierStokesPromoted dangerShellReceipt ≡ false

    conditionalMaxReceipt :
      Conditional.NSDangerShellMaxPrincipleConditionalProofReceipt zero

    conditionalMaxCircularityRecorded :
      Conditional.circularityIdentified conditionalMaxReceipt ≡ true

    conditionalMaxNonCircularOpen :
      Conditional.nonCircularWeakeningProved conditionalMaxReceipt ≡ false

    conditionalMaxKStarOpen :
      Conditional.nonCircularKStarDriftBoundOpen conditionalMaxReceipt ≡ true

    conditionalMaxNoClay :
      Conditional.clayNavierStokesPromoted conditionalMaxReceipt ≡ false

    adjacentLeakageReceipt :
      Leak.NSAdjacentShellLeakageBoundReceipt zero

    adjacentEdgeInfluxConditionallyStated :
      Leak.edgeInfluxBoundConditionallyStated adjacentLeakageReceipt ≡ true

    adjacentLeakageNotUnconditional :
      Leak.leakageBoundUnconditionallyProved adjacentLeakageReceipt ≡ false

    adjacentLeakageNoThetaPromotion :
      Leak.thetaPreservationProvedHere adjacentLeakageReceipt ≡ false

    adjacentLeakageNoClay :
      Leak.clayNavierStokesPromoted adjacentLeakageReceipt ≡ false

    fullIdentityReceipt :
      Full.NSTailFluxLPIdentityFullDerivationReceipt zero

    fullIdentityDerived :
      Full.lpIdentityDerivedHere fullIdentityReceipt ≡ true

    fullIdentityNoMovingCutoff :
      Full.movingCutoffTermAbsent fullIdentityReceipt ≡ true

    fullIdentityNoThetaProof :
      Full.thetaLessThanOneProvedHere fullIdentityReceipt ≡ false

    fullIdentityNoClay :
      Full.clayNavierStokesPromoted fullIdentityReceipt ≡ false

    paraproductReceipt :
      Paraproduct.ParaproductDecompositionReceipt

    paraproductDecomposed :
      Paraproduct.paraproductDecomposed paraproductReceipt ≡ true

    lowHighControlledButNotSufficient :
      Paraproduct.lowHighControlledByLinftyH1 paraproductReceipt ≡ true

    paraproductNoGlobalRegularity :
      Paraproduct.fullGlobalRegularityEstimate paraproductReceipt ≡ false

    paraproductNoClay :
      Paraproduct.clayNavierStokesPromoted paraproductReceipt ≡ false

    theoremTargets :
      List NonCircularKStarTheoremTarget

    theoremTargetsAreCanonical :
      theoremTargets ≡ canonicalNonCircularKStarTheoremTargets

    highHighClauses :
      List HighHighObstructionClause

    highHighClausesAreCanonical :
      highHighClauses ≡ canonicalHighHighObstructionClauses

    openObligations :
      List NonCircularKStarOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalNonCircularKStarOpenObligations

    forbiddenCircularInputs :
      List ForbiddenCircularInput

    forbiddenCircularInputsAreCanonical :
      forbiddenCircularInputs ≡ canonicalForbiddenCircularInputs

    continuationOrder :
      List TailContinuationOrder

    continuationOrderIsCanonical :
      continuationOrder ≡ canonicalTailContinuationOrder

    targetFormula :
      String

    targetFormulaIsCanonical :
      targetFormula ≡ nonCircularKStarTargetFormula

    obstructionStatement :
      String

    obstructionStatementIsCanonical :
      obstructionStatement ≡ highHighObstructionStatement

    openObligationSummary :
      String

    openObligationSummaryIsCanonical :
      openObligationSummary ≡ openObligationStatement

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundaryStatement

    exactTargetRecorded :
      Bool

    exactTargetRecordedIsTrue :
      exactTargetRecorded ≡ true

    lowHighIsCoreObstruction :
      Bool

    lowHighIsCoreObstructionIsFalse :
      lowHighIsCoreObstruction ≡ false

    highHighParaproductLoadBearing :
      Bool

    highHighParaproductLoadBearingIsTrue :
      highHighParaproductLoadBearing ≡ true

    lowHighRatioBelowThetaOneInDiagnostics :
      Bool

    lowHighRatioBelowThetaOneInDiagnosticsIsTrue :
      lowHighRatioBelowThetaOneInDiagnostics ≡ true

    highHighBarrierCrossedInDangerDiagnostics :
      Bool

    highHighBarrierCrossedInDangerDiagnosticsIsTrue :
      highHighBarrierCrossedInDangerDiagnostics ≡ true

    highHighHMinusHalfDefectTargetRecorded :
      Bool

    highHighHMinusHalfDefectTargetRecordedIsTrue :
      highHighHMinusHalfDefectTargetRecorded ≡ true

    hHalfSerrinBKMAssumed :
      Bool

    hHalfSerrinBKMAssumedIsFalse :
      hHalfSerrinBKMAssumed ≡ false

    nonCircularHighHighControlProvedHere :
      Bool

    nonCircularHighHighControlProvedHereIsFalse :
      nonCircularHighHighControlProvedHere ≡ false

    kStarDriftContainmentProvedHere :
      Bool

    kStarDriftContainmentProvedHereIsFalse :
      kStarDriftContainmentProvedHere ≡ false

    edgeInfluxBoundProvedHere :
      Bool

    edgeInfluxBoundProvedHereIsFalse :
      edgeInfluxBoundProvedHere ≡ false

    thetaPreservationProvedHere :
      Bool

    thetaPreservationProvedHereIsFalse :
      thetaPreservationProvedHere ≡ false

    tailToContinuationDischargedHere :
      Bool

    tailToContinuationDischargedHereIsFalse :
      tailToContinuationDischargedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSNonCircularKStarPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSNonCircularKStarPromotion →
      ⊥

open NSNonCircularKStarDriftBoundTargetReceipt public

canonicalNSNonCircularKStarDriftBoundTargetReceipt :
  NSNonCircularKStarDriftBoundTargetReceipt
canonicalNSNonCircularKStarDriftBoundTargetReceipt =
  record
    { status =
        nonCircularKStarDriftBoundExactTargetRecorded
    ; statusIsCanonical =
        refl
    ; obstructionReceipt =
        Obstruction.canonicalNSNonCircularObstructionReceipt
    ; obstructionHighHighControlOpen =
        refl
    ; obstructionNoSerrinOrBKM =
        refl
    ; obstructionNoClay =
        refl
    ; negativeSobolevReceipt =
        NegSob.canonicalNSNegativeSobolevDangerShellReceipt
    ; negativeSobolevTargetRecorded =
        refl
    ; negativeSobolevDualPairingRecorded =
        refl
    ; negativeSobolevDefectBoundOpen =
        refl
    ; negativeSobolevNoHOneHalfShortcut =
        refl
    ; negativeSobolevNoClay =
        refl
    ; tailToBKMReceipt =
        TailBKM.canonicalNSThetaTailToBKMBridgeReceipt
    ; tailToBKMKStarDriftOpen =
        refl
    ; tailToBKMCriterionOpen =
        refl
    ; tailToBKMNoClay =
        refl
    ; dangerShellReceipt =
        Danger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellTargetOpen =
        refl
    ; dangerShellEdgeLeakageOpen =
        refl
    ; dangerShellNoClay =
        refl
    ; conditionalMaxReceipt =
        Conditional.canonicalNSDangerShellMaxPrincipleConditionalProofReceipt
    ; conditionalMaxCircularityRecorded =
        refl
    ; conditionalMaxNonCircularOpen =
        refl
    ; conditionalMaxKStarOpen =
        refl
    ; conditionalMaxNoClay =
        refl
    ; adjacentLeakageReceipt =
        Leak.canonicalNSAdjacentShellLeakageBoundReceipt
    ; adjacentEdgeInfluxConditionallyStated =
        refl
    ; adjacentLeakageNotUnconditional =
        refl
    ; adjacentLeakageNoThetaPromotion =
        refl
    ; adjacentLeakageNoClay =
        refl
    ; fullIdentityReceipt =
        Full.canonicalNSTailFluxLPIdentityFullDerivationReceipt
    ; fullIdentityDerived =
        refl
    ; fullIdentityNoMovingCutoff =
        refl
    ; fullIdentityNoThetaProof =
        refl
    ; fullIdentityNoClay =
        refl
    ; paraproductReceipt =
        Paraproduct.canonicalParaproductDecompositionReceipt
    ; paraproductDecomposed =
        refl
    ; lowHighControlledButNotSufficient =
        refl
    ; paraproductNoGlobalRegularity =
        refl
    ; paraproductNoClay =
        refl
    ; theoremTargets =
        canonicalNonCircularKStarTheoremTargets
    ; theoremTargetsAreCanonical =
        refl
    ; highHighClauses =
        canonicalHighHighObstructionClauses
    ; highHighClausesAreCanonical =
        refl
    ; openObligations =
        canonicalNonCircularKStarOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; forbiddenCircularInputs =
        canonicalForbiddenCircularInputs
    ; forbiddenCircularInputsAreCanonical =
        refl
    ; continuationOrder =
        canonicalTailContinuationOrder
    ; continuationOrderIsCanonical =
        refl
    ; targetFormula =
        nonCircularKStarTargetFormula
    ; targetFormulaIsCanonical =
        refl
    ; obstructionStatement =
        highHighObstructionStatement
    ; obstructionStatementIsCanonical =
        refl
    ; openObligationSummary =
        openObligationStatement
    ; openObligationSummaryIsCanonical =
        refl
    ; promotionBoundary =
        promotionBoundaryStatement
    ; promotionBoundaryIsCanonical =
        refl
    ; exactTargetRecorded =
        true
    ; exactTargetRecordedIsTrue =
        refl
    ; lowHighIsCoreObstruction =
        false
    ; lowHighIsCoreObstructionIsFalse =
        refl
    ; highHighParaproductLoadBearing =
        true
    ; highHighParaproductLoadBearingIsTrue =
        refl
    ; lowHighRatioBelowThetaOneInDiagnostics =
        true
    ; lowHighRatioBelowThetaOneInDiagnosticsIsTrue =
        refl
    ; highHighBarrierCrossedInDangerDiagnostics =
        true
    ; highHighBarrierCrossedInDangerDiagnosticsIsTrue =
        refl
    ; highHighHMinusHalfDefectTargetRecorded =
        true
    ; highHighHMinusHalfDefectTargetRecordedIsTrue =
        refl
    ; hHalfSerrinBKMAssumed =
        false
    ; hHalfSerrinBKMAssumedIsFalse =
        refl
    ; nonCircularHighHighControlProvedHere =
        false
    ; nonCircularHighHighControlProvedHereIsFalse =
        refl
    ; kStarDriftContainmentProvedHere =
        false
    ; kStarDriftContainmentProvedHereIsFalse =
        refl
    ; edgeInfluxBoundProvedHere =
        false
    ; edgeInfluxBoundProvedHereIsFalse =
        refl
    ; thetaPreservationProvedHere =
        false
    ; thetaPreservationProvedHereIsFalse =
        refl
    ; tailToContinuationDischargedHere =
        false
    ; tailToContinuationDischargedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsNonCircularKStarPromotionImpossibleHere
    }

canonicalNSNonCircularKStarTargetRecorded :
  exactTargetRecorded canonicalNSNonCircularKStarDriftBoundTargetReceipt
  ≡
  true
canonicalNSNonCircularKStarTargetRecorded =
  refl

canonicalNSNonCircularKStarTargetNoClay :
  clayNavierStokesPromoted canonicalNSNonCircularKStarDriftBoundTargetReceipt
  ≡
  false
canonicalNSNonCircularKStarTargetNoClay =
  refl
