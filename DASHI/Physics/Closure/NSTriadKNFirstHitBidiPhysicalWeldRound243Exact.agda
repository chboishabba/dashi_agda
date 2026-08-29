module DASHI.Physics.Closure.NSTriadKNFirstHitBidiPhysicalWeldRound243Exact where

------------------------------------------------------------------------
-- ROUND243 / BIDI PHYSICAL WELD FOR THE FIRST-HIT EXTRACTION PATH
--
-- Backward consumer:
--   Round241 needs only a critical barrier K, a mixed-helicity defect
--   reduction
--
--     Qint <= C * K * Dint,
--
--   and a cutoff-independent integrated dissipation bound Dint <= D_*.
--
--   Round242 then needs threshold crossings plus one genuine first-hit law.
--
-- Forward producers:
--   * Round240 owns the literal NS Galerkin trajectory;
--   * Round142 identifies the helicity-sign action with normalized curl;
--   * the canonical G2 owner carries the exact/uniform Galerkin energy theorem;
--   * standard torus Sobolev analysis supplies H^(1/2)->L^3 and H^1->L^6;
--   * finite-dimensional ODE regularity supplies continuity/first hitting.
--
-- This module does NOT introduce a second trajectory or a second energy law.
-- Every quantitative receipt is indexed by the SAME Round240 trajectory.
-- It proves only the two bidi compiler steps:
--
--   same-trajectory W1 + W2 -> Round241 payment,
--   same-trajectory W3 + threshold crossings -> Round242 sequence.
--
-- The remaining source-level work is to instantiate the three analytic
-- receipts on the literal Round240 trajectory.  No Package-A/Clay promotion
-- is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNDefectFailureForcesCriticalBarrierRound241Exact as R241
import DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact as R242

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalBidi
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn =
    R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  ----------------------------------------------------------------------
  -- The weakest same-trajectory quantitative surface needed by Round241.
  --
  -- `CriticalBarrierTo cutoff terminal K` means the physical critical size
  -- of THIS trajectory is bounded by K on the relevant interval.  Its exact
  -- analytic realization is intentionally external: this file only ensures
  -- that W1/W2 cannot be supplied for an unrelated trajectory.
  ----------------------------------------------------------------------

  record SameTrajectoryW1W2
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      criticalSize : Nat → Time → ℚ
      defectIntegral : Nat → Time → ℚ
      dissipationIntegral : Nat → Time → ℚ

      interpolationConstant : ℚ
      dissipationBound : ℚ

      CriticalBarrierTo : Nat → Time → ℚ → Set

      -- W1 after time integration:
      -- Qint <= C * K * Dint whenever the actual trajectory has barrier K.
      mixedHelicityCriticalReduction :
        (cutoff : Nat) (terminal : Time) (K : ℚ) →
        CriticalBarrierTo cutoff terminal K →
        defectIntegral cutoff terminal
        ≤ interpolationConstant * K * dissipationIntegral cutoff terminal

      -- W2 numeric projection of the canonical Galerkin energy theorem.
      integratedDissipationBound :
        (cutoff : Nat) (terminal : Time) →
        dissipationIntegral cutoff terminal ≤ dissipationBound

      -- Exactly the sign fact consumed by Round241's scalar compiler.
      scaledBarrierNonnegative :
        (cutoff : Nat) (terminal : Time) (K : ℚ) →
        CriticalBarrierTo cutoff terminal K →
        0ℚ ≤ interpolationConstant * K

  open SameTrajectoryW1W2 public

  sameTrajectoryW1W2BuildRound241Payment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : SameTrajectoryW1W2 T) →
    (cutoff : Nat) (terminal : Time) (K : ℚ) →
    CriticalBarrierTo R cutoff terminal K →
    R241.CriticalBarrierDefectPayment
  sameTrajectoryW1W2BuildRound241Payment T R cutoff terminal K barrier = record
    { R241.defectIntegral = defectIntegral R cutoff terminal
    ; R241.interpolationConstant = interpolationConstant R
    ; R241.criticalBarrier = K
    ; R241.dissipationIntegral = dissipationIntegral R cutoff terminal
    ; R241.dissipationBound = dissipationBound R
    ; R241.scaledBarrierNN =
        scaledBarrierNonnegative R cutoff terminal K barrier
    ; R241.defectReducedToBarrierTimesDissipation =
        mixedHelicityCriticalReduction R cutoff terminal K barrier
    ; R241.dissipationUniformlyBounded =
        integratedDissipationBound R cutoff terminal
    }

  sameTrajectoryBarrierPaysDefect :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : SameTrajectoryW1W2 T) →
    (cutoff : Nat) (terminal : Time) (K : ℚ) →
    (barrier : CriticalBarrierTo R cutoff terminal K) →
    defectIntegral R cutoff terminal
    ≤ interpolationConstant R * K * dissipationBound R
  sameTrajectoryBarrierPaysDefect T R cutoff terminal K barrier =
    R241.boundedCriticalBarrierPaysDefect
      (sameTrajectoryW1W2BuildRound241Payment
        T R cutoff terminal K barrier)

  ----------------------------------------------------------------------
  -- W3: bind the first-hit law to the critical-size observable of the SAME
  -- trajectory/receipt.  Round242 already owns the generic selector compiler.
  ----------------------------------------------------------------------

  record SameTrajectoryW3
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : SameTrajectoryW1W2 T)
      (Before : Time → Time → Set)
      (threshold : ℚ) : Set₁ where
    field
      firstHitLaw :
        R242.FirstHitLaw Time Before (criticalSize R) threshold

  open SameTrajectoryW3 public

  sameTrajectoryW3BuildsCriticalSequence :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : SameTrajectoryW1W2 T) →
    {Before : Time → Time → Set} →
    {threshold : ℚ} →
    (W3 : SameTrajectoryW3 T R Before threshold) →
    (cutoffs : Nat → Nat) →
    (crosses : (n : Nat) →
      R242.ThresholdCrossing
        Time (criticalSize R) threshold (cutoffs n)) →
    R242.CriticalFirstHitSequence Time (criticalSize R) threshold
  sameTrajectoryW3BuildsCriticalSequence T R W3 cutoffs crosses =
    R242.firstHitLawBuildsCriticalSequence
      (firstHitLaw W3) cutoffs crosses

round243SameTrajectoryBidiCompilerClosed : Bool
round243SameTrajectoryBidiCompilerClosed = true

round243W1PhysicalSobolevNormalizedCurlInstanceInstalled : Bool
round243W1PhysicalSobolevNormalizedCurlInstanceInstalled = false

round243W2CanonicalG2NumericDissipationProjectionInstalled : Bool
round243W2CanonicalG2NumericDissipationProjectionInstalled = false

round243W3FiniteDimensionalFirstHitInstanceInstalled : Bool
round243W3FiniteDimensionalFirstHitInstanceInstalled = false

round243Round241PaymentPhysicallyInstantiated : Bool
round243Round241PaymentPhysicallyInstantiated = false

round243Round242CriticalSequencePhysicallyInstantiated : Bool
round243Round242CriticalSequencePhysicallyInstantiated = false

round243PackageAClosed : Bool
round243PackageAClosed = false

round243ClayPromotion : Bool
round243ClayPromotion = false

round243SameTrajectoryBidiCompilerClosedIsTrue :
  round243SameTrajectoryBidiCompilerClosed ≡ true
round243SameTrajectoryBidiCompilerClosedIsTrue = refl

round243W1PhysicalSobolevNormalizedCurlInstanceInstalledIsFalse :
  round243W1PhysicalSobolevNormalizedCurlInstanceInstalled ≡ false
round243W1PhysicalSobolevNormalizedCurlInstanceInstalledIsFalse = refl

round243W2CanonicalG2NumericDissipationProjectionInstalledIsFalse :
  round243W2CanonicalG2NumericDissipationProjectionInstalled ≡ false
round243W2CanonicalG2NumericDissipationProjectionInstalledIsFalse = refl

round243W3FiniteDimensionalFirstHitInstanceInstalledIsFalse :
  round243W3FiniteDimensionalFirstHitInstanceInstalled ≡ false
round243W3FiniteDimensionalFirstHitInstanceInstalledIsFalse = refl

round243PackageAClosedIsFalse : round243PackageAClosed ≡ false
round243PackageAClosedIsFalse = refl

round243ClayPromotionIsFalse : round243ClayPromotion ≡ false
round243ClayPromotionIsFalse = refl
