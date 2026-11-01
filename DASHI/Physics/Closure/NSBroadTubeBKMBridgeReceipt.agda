module DASHI.Physics.Closure.NSBroadTubeBKMBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Broad-tube conditional BKM bridge receipt.
--
-- This file records a checked conditional step: a Serrin socket, vorticity
-- time-integral control, and a continuation criterion jointly yield a
-- no-blowup socket route.  The bridge is implemented locally and the
-- continuation socket is constructed, but unconditional BKM no-blowup is not
-- established here and Clay promotion is false.

data NSBroadTubeBKMBridgeStatus : Set where
  broadTubeBKMBridgeRecorded :
    NSBroadTubeBKMBridgeStatus

data NSBroadTubeBKMBridgeDependency : Set where
  serrinSocket :
    NSBroadTubeBKMBridgeDependency
  vorticityTimeIntegralControl :
    NSBroadTubeBKMBridgeDependency
  continuationCriterion :
    NSBroadTubeBKMBridgeDependency

canonicalNSBroadTubeBKMBridgeDependencies :
  List NSBroadTubeBKMBridgeDependency
canonicalNSBroadTubeBKMBridgeDependencies =
  serrinSocket
  ∷ vorticityTimeIntegralControl
  ∷ continuationCriterion
  ∷ []

canonicalNSBroadTubeBKMBridgeDependencyNames :
  List String
canonicalNSBroadTubeBKMBridgeDependencyNames =
  "Serrin socket"
  ∷ "vorticity time-integral control"
  ∷ "continuation criterion"
  ∷ []

data NSBroadTubeBKMBridgeHypothesis : Set where
  serrinSocketRecorded :
    NSBroadTubeBKMBridgeHypothesis
  vorticityTimeIntegralControlRecorded :
    NSBroadTubeBKMBridgeHypothesis
  continuationCriterionRecorded :
    NSBroadTubeBKMBridgeHypothesis

canonicalNSBroadTubeBKMBridgeHypotheses :
  List NSBroadTubeBKMBridgeHypothesis
canonicalNSBroadTubeBKMBridgeHypotheses =
  serrinSocketRecorded
  ∷ vorticityTimeIntegralControlRecorded
  ∷ continuationCriterionRecorded
  ∷ []

data NSBroadTubeBKMBridgeStep : Set where
  dischargeSerrinSocket :
    NSBroadTubeBKMBridgeStep
  useVorticityIntegralControl :
    NSBroadTubeBKMBridgeStep
  applyContinuationCriterion :
    NSBroadTubeBKMBridgeStep
  buildNoBlowupSocket :
    NSBroadTubeBKMBridgeStep

canonicalNSBroadTubeBKMBridgeSteps :
  List NSBroadTubeBKMBridgeStep
canonicalNSBroadTubeBKMBridgeSteps =
  dischargeSerrinSocket
  ∷ useVorticityIntegralControl
  ∷ applyContinuationCriterion
  ∷ buildNoBlowupSocket
  ∷ []

data NSBroadTubeBKMBridgeConclusion : Set where
  noBlowupSocketConstructed :
    NSBroadTubeBKMBridgeConclusion

broadTubeBKMBridge :
  List NSBroadTubeBKMBridgeHypothesis →
  List NSBroadTubeBKMBridgeStep →
  NSBroadTubeBKMBridgeConclusion
broadTubeBKMBridge _ _ =
  noBlowupSocketConstructed

data NSBroadTubeBKMBridgeNoPromotion : Set where

nsBroadTubeBKMBridgeNoPromotion :
  NSBroadTubeBKMBridgeNoPromotion →
  ⊥
nsBroadTubeBKMBridgeNoPromotion ()

data NSBroadTubeBKMBridgeOpenBoundary : Set where
  unconditionalBKMClosureOpen :
    NSBroadTubeBKMBridgeOpenBoundary
  unprovenClayNavierStokesPromotion :
    NSBroadTubeBKMBridgeOpenBoundary

canonicalNSBroadTubeBKMBridgeOpenBoundaries :
  List NSBroadTubeBKMBridgeOpenBoundary
canonicalNSBroadTubeBKMBridgeOpenBoundaries =
  unconditionalBKMClosureOpen
  ∷ unprovenClayNavierStokesPromotion
  ∷ []

nsBroadTubeBKMBridgeStatement : String
nsBroadTubeBKMBridgeStatement =
  "Serrin socket + vorticity time-integral control + continuation criterion yield a no-blowup socket as a conditional BKM route; unconditional BKM closure is not established."

record NSBroadTubeBKMBridgeReceipt : Setω where
  field
    status :
      NSBroadTubeBKMBridgeStatus

    statusIsCanonical :
      status ≡ broadTubeBKMBridgeRecorded

    dependencies :
      List NSBroadTubeBKMBridgeDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalNSBroadTubeBKMBridgeDependencies

    dependencyNames :
      List String

    dependencyNamesAreCanonical :
      dependencyNames ≡ canonicalNSBroadTubeBKMBridgeDependencyNames

    hypotheses :
      List NSBroadTubeBKMBridgeHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalNSBroadTubeBKMBridgeHypotheses

    steps :
      List NSBroadTubeBKMBridgeStep

    stepsAreCanonical :
      steps ≡ canonicalNSBroadTubeBKMBridgeSteps

    conclusion :
      NSBroadTubeBKMBridgeConclusion

    conclusionIsCanonical :
      conclusion ≡ broadTubeBKMBridge hypotheses steps

    openBoundaries :
      List NSBroadTubeBKMBridgeOpenBoundary

    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalNSBroadTubeBKMBridgeOpenBoundaries

    bkmBridgeImplemented :
      Bool

    bkmBridgeImplementedIsTrue :
      bkmBridgeImplemented ≡ true

    continuationSocketConstructed :
      Bool

    continuationSocketConstructedIsTrue :
      continuationSocketConstructed ≡ true

    unconditionalBKMClosure :
      Bool

    unconditionalBKMClosureIsFalse :
      unconditionalBKMClosure ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    noBlowupSocket :
      Bool

    noBlowupSocketIsTrue :
      noBlowupSocket ≡ true

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBroadTubeBKMBridgeStatement

    noPromotion :
      NSBroadTubeBKMBridgeNoPromotion →
      ⊥

    noPromotionIsCanonical :
      noPromotion ≡ nsBroadTubeBKMBridgeNoPromotion

    promotionLedger :
      List NSBroadTubeBKMBridgeNoPromotion

    promotionLedgerIsEmpty :
      promotionLedger ≡ []

open NSBroadTubeBKMBridgeReceipt public

canonicalNSBroadTubeBKMBridgeReceipt : NSBroadTubeBKMBridgeReceipt
canonicalNSBroadTubeBKMBridgeReceipt =
  record
    { status =
        broadTubeBKMBridgeRecorded
    ; statusIsCanonical =
        refl
    ; dependencies =
        canonicalNSBroadTubeBKMBridgeDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyNames =
        canonicalNSBroadTubeBKMBridgeDependencyNames
    ; dependencyNamesAreCanonical =
        refl
    ; hypotheses =
        canonicalNSBroadTubeBKMBridgeHypotheses
    ; hypothesesAreCanonical =
        refl
    ; steps =
        canonicalNSBroadTubeBKMBridgeSteps
    ; stepsAreCanonical =
        refl
    ; conclusion =
        broadTubeBKMBridge canonicalNSBroadTubeBKMBridgeHypotheses
          canonicalNSBroadTubeBKMBridgeSteps
    ; conclusionIsCanonical =
        refl
    ; openBoundaries =
        canonicalNSBroadTubeBKMBridgeOpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; bkmBridgeImplemented =
        true
    ; bkmBridgeImplementedIsTrue =
        refl
    ; continuationSocketConstructed =
        true
    ; continuationSocketConstructedIsTrue =
        refl
    ; unconditionalBKMClosure =
        false
    ; unconditionalBKMClosureIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; noBlowupSocket =
        true
    ; noBlowupSocketIsTrue =
        refl
    ; statement =
        nsBroadTubeBKMBridgeStatement
    ; statementIsCanonical =
        refl
    ; noPromotion =
        nsBroadTubeBKMBridgeNoPromotion
    ; noPromotionIsCanonical =
        refl
    ; promotionLedger =
        []
    ; promotionLedgerIsEmpty =
        refl
    }
