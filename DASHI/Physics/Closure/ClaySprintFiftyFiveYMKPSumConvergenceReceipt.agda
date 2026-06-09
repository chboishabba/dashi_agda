module DASHI.Physics.Closure.ClaySprintFiftyFiveYMKPSumConvergenceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_)
open import Data.Nat.Properties as NatP using (m≤m+n)

import DASHI.Physics.Closure.ClaySprintFiftyFourYMInductiveDiameterKPReceipt
  as Sprint54YM

------------------------------------------------------------------------
-- Sprint 55 Yang-Mills KP sum convergence correction.
--
-- Sprint 54 recorded that the blocked contour/action row at beta = 16.7
-- clears a finite-prefix branch check.  Sprint 55 separates the one-step
-- diameter ratio from the weighted KP polymer sum:
--
--   raw ratio        = exp(a - beta*c_min) ~= 0.0289727
--   activity q       = c_combo * raw ratio ~= 0.231782 < 1
--   weighted KP tail = branching * q       ~= 1.85426 > 1
--
-- Thus q < 1 is not enough to close AllDiameterKPActivityBound under the
-- current p=7, c_combo=8, branching=8 bookkeeping.  The corrected beta
-- threshold for the weighted KP tail is about 19.252, so beta = 16.7 is
-- insufficient.  This file records that blocker and keeps YM unpromoted.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint55YMKPGate : Set where
  gateGeometricRatioUniform :
    Sprint55YMKPGate

  gateQBelowOne :
    Sprint55YMKPGate

  gateWeightedKPSumConvergence :
    Sprint55YMKPGate

  gateAllDiameterKPActivityBound :
    Sprint55YMKPGate

  gateBalabanRGScaleTransfer :
    Sprint55YMKPGate

  gateContinuumRhoLeakage :
    Sprint55YMKPGate

  gateOSWightmanMassGap :
    Sprint55YMKPGate

canonicalSprint55YMKPGates :
  List Sprint55YMKPGate
canonicalSprint55YMKPGates =
  gateGeometricRatioUniform
  ∷ gateQBelowOne
  ∷ gateWeightedKPSumConvergence
  ∷ gateAllDiameterKPActivityBound
  ∷ gateBalabanRGScaleTransfer
  ∷ gateContinuumRhoLeakage
  ∷ gateOSWightmanMassGap
  ∷ []

data Sprint55YMKPStatus : Set where
  qBelowOneButWeightedKPSumDiverges :
    Sprint55YMKPStatus

  currentBetaBlockedInsufficientForKPSum :
    Sprint55YMKPStatus

  balabanTransferStillOpen :
    Sprint55YMKPStatus

  noClayYangMillsPromotion :
    Sprint55YMKPStatus

canonicalSprint55YMKPStatuses :
  List Sprint55YMKPStatus
canonicalSprint55YMKPStatuses =
  qBelowOneButWeightedKPSumDiverges
  ∷ currentBetaBlockedInsufficientForKPSum
  ∷ balabanTransferStillOpen
  ∷ noClayYangMillsPromotion
  ∷ []

data Sprint55YMKPPromotion : Set where

sprint55YMKPPromotionImpossibleHere :
  Sprint55YMKPPromotion →
  ⊥
sprint55YMKPPromotionImpossibleHere ()

p7Prime :
  Nat
p7Prime =
  7

btBranchingFactor :
  Nat
btBranchingFactor =
  8

comboFactor :
  Nat
comboFactor =
  8

qNumeratorMicro :
  Nat
qNumeratorMicro =
  231782

qDenominatorMicro :
  Nat
qDenominatorMicro =
  1000000

branchingTimesQNumeratorMicro :
  Nat
branchingTimesQNumeratorMicro =
  1854256

branchingTimesQDenominatorMicro :
  Nat
branchingTimesQDenominatorMicro =
  1000000

betaBlockedMilli :
  Nat
betaBlockedMilli =
  16700

betaNeededForKPSumMilli :
  Nat
betaNeededForKPSumMilli =
  19252

qBelowOneWitness :
  qNumeratorMicro < qDenominatorMicro
qBelowOneWitness =
  NatP.m≤m+n 231783 768217

weightedKPSumDivergesWitness :
  branchingTimesQDenominatorMicro < branchingTimesQNumeratorMicro
weightedKPSumDivergesWitness =
  NatP.m≤m+n 1000001 854255

currentBetaBlockedInsufficientWitness :
  betaBlockedMilli < betaNeededForKPSumMilli
currentBetaBlockedInsufficientWitness =
  NatP.m≤m+n 16701 2551

sprint55YMKPBoundary :
  String
sprint55YMKPBoundary =
  "Sprint 55 records that q<1 at beta=16.7 is distinct from KP weighted-sum convergence: with branching=8 and c_combo=8, branching*q ~= 1.854 > 1, so AllDiameterKPActivityBound remains blocked and beta_needed ~= 19.252."

record ClaySprintFiftyFiveYMKPSumConvergenceReceipt : Setω where
  field
    sprint54YMReceipt :
      Sprint54YM.ClaySprintFiftyFourYMInductiveDiameterKPReceipt

    sprint54NoClayYM :
      Sprint54YM.clayYangMillsPromoted sprint54YMReceipt ≡ false

    p :
      Nat

    pIsSeven :
      p ≡ p7Prime

    branching :
      Nat

    branchingIsEight :
      branching ≡ btBranchingFactor

    cCombo :
      Nat

    cComboIsEight :
      cCombo ≡ comboFactor

    betaBlocked :
      Scalar

    betaNeededForKPSum :
      Scalar

    qAtBetaBlocked :
      Scalar

    branchingTimesQ :
      Scalar

    qBelowOne :
      Bool

    qBelowOneIsTrue :
      qBelowOne ≡ true

    qBelowOneArithmetic :
      qNumeratorMicro < qDenominatorMicro

    kpSumConverges :
      Bool

    kpSumConvergesIsFalse :
      kpSumConverges ≡ false

    kpSumDivergesArithmetic :
      branchingTimesQDenominatorMicro < branchingTimesQNumeratorMicro

    betaBlockedInsufficientForKPSum :
      Bool

    betaBlockedInsufficientForKPSumIsTrue :
      betaBlockedInsufficientForKPSum ≡ true

    betaBlockedInsufficientArithmetic :
      betaBlockedMilli < betaNeededForKPSumMilli

    allDiameterKPActivityBound :
      Bool

    allDiameterKPActivityBoundIsFalse :
      allDiameterKPActivityBound ≡ false

    balabanRGScaleTransfer :
      Bool

    balabanRGScaleTransferIsFalse :
      balabanRGScaleTransfer ≡ false

    continuumUniformRhoBound :
      Bool

    continuumUniformRhoBoundIsFalse :
      continuumUniformRhoBound ≡ false

    continuumUniformLeakageBound :
      Bool

    continuumUniformLeakageBoundIsFalse :
      continuumUniformLeakageBound ≡ false

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    gates :
      List Sprint55YMKPGate

    gatesAreCanonical :
      gates ≡ canonicalSprint55YMKPGates

    statuses :
      List Sprint55YMKPStatus

    statusesAreCanonical :
      statuses ≡ canonicalSprint55YMKPStatuses

    promotions :
      List Sprint55YMKPPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotion :
      Sprint55YMKPPromotion →
      ⊥

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ sprint55YMKPBoundary

open ClaySprintFiftyFiveYMKPSumConvergenceReceipt public

canonicalClaySprintFiftyFiveYMKPSumConvergenceReceipt :
  ClaySprintFiftyFiveYMKPSumConvergenceReceipt
canonicalClaySprintFiftyFiveYMKPSumConvergenceReceipt =
  record
    { sprint54YMReceipt =
        Sprint54YM.canonicalClaySprintFiftyFourYMInductiveDiameterKPReceipt
    ; sprint54NoClayYM =
        refl
    ; p =
        p7Prime
    ; pIsSeven =
        refl
    ; branching =
        btBranchingFactor
    ; branchingIsEight =
        refl
    ; cCombo =
        comboFactor
    ; cComboIsEight =
        refl
    ; betaBlocked =
        "16.7"
    ; betaNeededForKPSum =
        "19.251582989089552"
    ; qAtBetaBlocked =
        "0.23178189475262734"
    ; branchingTimesQ =
        "1.8542551580210187"
    ; qBelowOne =
        true
    ; qBelowOneIsTrue =
        refl
    ; qBelowOneArithmetic =
        qBelowOneWitness
    ; kpSumConverges =
        false
    ; kpSumConvergesIsFalse =
        refl
    ; kpSumDivergesArithmetic =
        weightedKPSumDivergesWitness
    ; betaBlockedInsufficientForKPSum =
        true
    ; betaBlockedInsufficientForKPSumIsTrue =
        refl
    ; betaBlockedInsufficientArithmetic =
        currentBetaBlockedInsufficientWitness
    ; allDiameterKPActivityBound =
        false
    ; allDiameterKPActivityBoundIsFalse =
        refl
    ; balabanRGScaleTransfer =
        false
    ; balabanRGScaleTransferIsFalse =
        refl
    ; continuumUniformRhoBound =
        false
    ; continuumUniformRhoBoundIsFalse =
        refl
    ; continuumUniformLeakageBound =
        false
    ; continuumUniformLeakageBoundIsFalse =
        refl
    ; clayYangMillsPromotedIsFalse =
        refl
    ; gates =
        canonicalSprint55YMKPGates
    ; gatesAreCanonical =
        refl
    ; statuses =
        canonicalSprint55YMKPStatuses
    ; statusesAreCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotion =
        sprint55YMKPPromotionImpossibleHere
    ; boundary =
        sprint55YMKPBoundary
    ; boundaryIsCanonical =
        refl
    }
