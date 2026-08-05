module DASHI.Physics.Closure.NSTriadKNMisurSecondCommutationSourceAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Marin Mišur.
-- Title: "Global L^p Second Commutation Lemma".
-- arXiv:2608.01216v1 (2 August 2026; work in progress).
-- arXiv DOI: 10.48550/arXiv.2608.01216.
--
-- Authors: Luc Tartar and the H-measure/H-distribution literature cited by
-- Mišur.  This module imports no theorem from the preprint as an axiom.
--
-- PURPOSE
-- The phrase "second commutation lemma" in Mišur's paper names a
-- microlocal pseudo-differential result:
--
--   partial_j [A_a , M_b] = Op(xi_j {a,b}) + compact remainder.
--
-- Its Appendix A gives an explicit Taylor-remainder kernel.  That is useful
-- structural evidence for retaining the second-order remainder, but it is not
-- the Littlewood--Paley paired-moment estimate required by the terminal-window
-- Navier--Stokes lane.  In particular the paper does not by itself provide
--
--   lambda_q^-2,
--   the four Bony interaction estimates, or
--   terminal-dissipation smallness.
--
-- The finite theorem below formalises the exact Taylor split used by the
-- paper and gives a type-level no-confusion theorem between the two targets.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

data CommutationLane : Set where
  microlocalDerivativeCompactRemainder : CommutationLane
  dyadicPairedSecondMoment : CommutationLane

misurLane : CommutationLane
misurLane = microlocalDerivativeCompactRemainder

terminalNavierStokesLane : CommutationLane
terminalNavierStokesLane = dyadicPairedSecondMoment

misurLaneIsNotTheDyadicMomentLane :
  misurLane ≢ terminalNavierStokesLane
misurLaneIsNotTheDyadicMomentLane ()

record TaylorKernelSample : Set where
  constructor taylor-kernel-sample
  field
    kernelDerivative : ℚ
    valueAtY valueAtX : ℚ
    gradientAtX displacement : ℚ

open TaylorKernelSample public

linearTaylorPart : TaylorKernelSample → ℚ
linearTaylorPart sample =
  gradientAtX sample * displacement sample

secondTaylorRemainder : TaylorKernelSample → ℚ
secondTaylorRemainder sample =
  valueAtY sample
  - valueAtX sample
  - linearTaylorPart sample

rawDifferentiatedKernelTerm : TaylorKernelSample → ℚ
rawDifferentiatedKernelTerm sample =
  kernelDerivative sample
  * (valueAtY sample - valueAtX sample)

principalLinearKernelTerm : TaylorKernelSample → ℚ
principalLinearKernelTerm sample =
  kernelDerivative sample * linearTaylorPart sample

remainderKernelTerm : TaylorKernelSample → ℚ
remainderKernelTerm sample =
  kernelDerivative sample * secondTaylorRemainder sample

exactTaylorKernelSplit :
  (sample : TaylorKernelSample) →
  rawDifferentiatedKernelTerm sample
  ≡ principalLinearKernelTerm sample + remainderKernelTerm sample
exactTaylorKernelSplit sample =
  solve
    ( kernelDerivative sample
    ∷ valueAtY sample
    ∷ valueAtX sample
    ∷ gradientAtX sample
    ∷ displacement sample
    ∷ [])

record SecondCommutationDeliverables : Set₁ where
  constructor second-commutation-deliverables
  field
    principalPoissonSymbol : Set
    compactRemainder : Set
    dyadicSecondMomentScaling : Set
    terminalDissipationEstimate : Set

-- The first two fields are the theorem shape of Mišur's paper.  The latter
-- two are deliberately separate producer types in the DASHI terminal lane.
-- No inhabitant is manufactured for any of these analytic proposition slots.
