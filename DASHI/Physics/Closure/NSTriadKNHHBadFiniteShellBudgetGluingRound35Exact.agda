module DASHI.Physics.Closure.NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact where

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
-- Repackage the exact Round-34 summability theorem as a finite gluing law
-- between the internal shell budget and the unresolved cutoff boundary seam.
-- For the uniquely forced HH-bad gain g_q(eta), define
--
--   I_Q = sum_{q=0}^Q g_q(eta),
--   B_Q = eta 2^(-(Q+1)).
--
-- Then I_Q + B_Q = eta exactly.  Advancing the cutoff moves precisely one
-- new shell gain from the boundary budget into the internal budget while the
-- residual boundary halves.  Thus the finite cutoff decomposition preserves
-- the same global eta resource at every stage.
--
-- This is the exact algebra needed later by shell-cutoff passage: it does not
-- assert a physical trajectory produces the profile, and it does not replace
-- the still-open analytic HH-bad gain theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadSummableDyadicGainRound34Exact as Sum

record FiniteShellBudgetGluing (eta : ℚ) (lastShell : Nat) : Set where
  constructor finite-shell-budget-gluing
  field
    internalBudget : ℚ
    boundaryBudget : ℚ

    internalExact :
      internalBudget ≡ Sum.requiredGainPrefix eta lastShell

    boundaryExact :
      boundaryBudget
      ≡ eta * Sharp.inverseDyadicScale (suc lastShell)

    gluedBudgetExact :
      internalBudget + boundaryBudget ≡ eta

open FiniteShellBudgetGluing public

canonicalFiniteShellBudgetGluing :
  ∀ eta lastShell → FiniteShellBudgetGluing eta lastShell
canonicalFiniteShellBudgetGluing eta lastShell =
  finite-shell-budget-gluing
    (Sum.requiredGainPrefix eta lastShell)
    (eta * Sharp.inverseDyadicScale (suc lastShell))
    refl refl
    (Sum.requiredGainPrefixPlusTail eta lastShell)

internalBudgetClosedForm :
  ∀ eta lastShell →
  internalBudget (canonicalFiniteShellBudgetGluing eta lastShell)
  ≡ eta - eta * Sharp.inverseDyadicScale (suc lastShell)
internalBudgetClosedForm = Sum.requiredGainPrefixClosedForm

boundaryBudgetHalves :
  ∀ eta lastShell →
  boundaryBudget (canonicalFiniteShellBudgetGluing eta (suc lastShell))
  ≡ Sharp.half
      * boundaryBudget (canonicalFiniteShellBudgetGluing eta lastShell)
boundaryBudgetHalves = Sum.requiredGainTailHalves

internalBudgetIncrementIsNextGain :
  ∀ eta lastShell →
  internalBudget (canonicalFiniteShellBudgetGluing eta (suc lastShell))
    - internalBudget (canonicalFiniteShellBudgetGluing eta lastShell)
  ≡ Sharp.requiredHHBadGain eta (suc lastShell)
internalBudgetIncrementIsNextGain = Sum.requiredGainPrefixIncrement

cutoffAdvanceConservesTotalBudget :
  ∀ eta lastShell →
  internalBudget (canonicalFiniteShellBudgetGluing eta (suc lastShell))
    + boundaryBudget (canonicalFiniteShellBudgetGluing eta (suc lastShell))
  ≡ internalBudget (canonicalFiniteShellBudgetGluing eta lastShell)
    + boundaryBudget (canonicalFiniteShellBudgetGluing eta lastShell)
cutoffAdvanceConservesTotalBudget =
  Sum.requiredGainPrefixSuccessorConservation

record ShellBudgetTransferStep (eta : ℚ) (lastShell : Nat) : Set where
  constructor shell-budget-transfer-step
  field
    oldBudget : FiniteShellBudgetGluing eta lastShell
    newBudget : FiniteShellBudgetGluing eta (suc lastShell)

    transferredShellGain : ℚ
    transferredShellGainExact :
      transferredShellGain
      ≡ Sharp.requiredHHBadGain eta (suc lastShell)

    internalGainExact :
      internalBudget newBudget - internalBudget oldBudget
      ≡ transferredShellGain

    totalResourceInvariant :
      internalBudget newBudget + boundaryBudget newBudget
      ≡ internalBudget oldBudget + boundaryBudget oldBudget

open ShellBudgetTransferStep public

canonicalShellBudgetTransferStep :
  ∀ eta lastShell → ShellBudgetTransferStep eta lastShell
canonicalShellBudgetTransferStep eta lastShell =
  shell-budget-transfer-step
    (canonicalFiniteShellBudgetGluing eta lastShell)
    (canonicalFiniteShellBudgetGluing eta (suc lastShell))
    (Sharp.requiredHHBadGain eta (suc lastShell))
    refl
    (internalBudgetIncrementIsNextGain eta lastShell)
    (cutoffAdvanceConservesTotalBudget eta lastShell)

hhBadFiniteShellBudgetGluingClosed : Bool
hhBadFiniteShellBudgetGluingClosed = true

physicalHHBadShellBudgetProduced : Bool
physicalHHBadShellBudgetProduced = false

hhBadFiniteShellBudgetGluingClosedIsTrue :
  hhBadFiniteShellBudgetGluingClosed ≡ true
hhBadFiniteShellBudgetGluingClosedIsTrue = refl

physicalHHBadShellBudgetProducedIsFalse :
  physicalHHBadShellBudgetProduced ≡ false
physicalHHBadShellBudgetProducedIsFalse = refl
