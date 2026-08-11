module DASHI.Physics.Closure.NSTriadKNHHBadNoScaleFreeGainRound33Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the sharp dyadic calibration theorem to a no-go statement.
-- If one scale-independent gain calibrates both shell q and shell q+1
-- exactly against the raw HH-bad ratio, then the owner allocation eta must
-- be zero.  Therefore every nonzero owner allocation rules out a constant
-- exact gain even across two adjacent dyadic shells.
--
-- This is the finite algebraic form of the cutoff obstruction: a viable
-- physical mechanism must carry shell dependence, signed cancellation, or a
-- stronger inequality.  The theorem does not assume or manufacture such a
-- mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

sameGainAtAdjacentShellsForcesZeroAllocation :
  ∀ eta shell gain →
  gain * Sharp.rawHHBadRatio shell ≡ eta →
  gain * Sharp.rawHHBadRatio (suc shell) ≡ eta →
  eta ≡ 0ℚ
sameGainAtAdjacentShellsForcesZeroAllocation
    eta shell gain baseCalibration successorCalibration =
  let
    successorAsTwice :
      gain * Sharp.rawHHBadRatio (suc shell)
      ≡ Sharp.two * (gain * Sharp.rawHHBadRatio shell)
    successorAsTwice =
      trans
        (cong (gain *_) (Sharp.rawHHBadRatioDoubles shell))
        (ℚRing.solve-∀
          gain (Sharp.rawHHBadRatio shell))

    twiceAllocationEqualsAllocation :
      Sharp.two * eta ≡ eta
    twiceAllocationEqualsAllocation =
      trans
        (sym
          (cong (Sharp.two *_)
            baseCalibration))
        (trans
          (sym successorAsTwice)
          successorCalibration)

    shifted :
      Sharp.two * eta - eta ≡ eta - eta
    shifted =
      cong (λ value → value - eta)
        twiceAllocationEqualsAllocation

    leftNormal : Sharp.two * eta - eta ≡ eta
    leftNormal = ℚRing.solve-∀ eta

    rightNormal : eta - eta ≡ 0ℚ
    rightNormal = ℚRing.solve-∀ eta
  in
  trans
    (sym leftNormal)
    (trans shifted rightNormal)

record NonzeroOwnerAllocation (eta : ℚ) : Set where
  constructor nonzero-owner-allocation
  field
    allocationNonzero : eta ≡ 0ℚ → ⊥

open NonzeroOwnerAllocation public

sameGainAtAdjacentShellsImpossible :
  ∀ {eta shell gain} →
  NonzeroOwnerAllocation eta →
  gain * Sharp.rawHHBadRatio shell ≡ eta →
  gain * Sharp.rawHHBadRatio (suc shell) ≡ eta →
  ⊥
sameGainAtAdjacentShellsImpossible
    {eta} {shell} {gain} allocation
    baseCalibration successorCalibration =
  allocationNonzero allocation
    (sameGainAtAdjacentShellsForcesZeroAllocation
      eta shell gain baseCalibration successorCalibration)

record ScaleFreeExactHHBadCalibration
    (eta : ℚ) : Set where
  constructor scale-free-exact-hhbad-calibration
  field
    gain : ℚ
    calibratesEveryShell :
      ∀ shell → gain * Sharp.rawHHBadRatio shell ≡ eta

open ScaleFreeExactHHBadCalibration public

nonzeroAllocationRefutesScaleFreeExactCalibration :
  ∀ {eta} →
  NonzeroOwnerAllocation eta →
  ScaleFreeExactHHBadCalibration eta →
  ⊥
nonzeroAllocationRefutesScaleFreeExactCalibration
    allocation calibration =
  sameGainAtAdjacentShellsImpossible
    allocation
    (calibratesEveryShell calibration 0)
    (calibratesEveryShell calibration 1)

scaleFreeExactGainNoGoClosed : Bool
scaleFreeExactGainNoGoClosed = true

scaleFreeExactGainNoGoClosedIsTrue :
  scaleFreeExactGainNoGoClosed ≡ true
scaleFreeExactGainNoGoClosedIsTrue = refl
