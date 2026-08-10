module DASHI.Physics.Closure.NSTriadKNShellBudgetProjectiveTelescopeRound37Exact where

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
-- Round 36 packaged the finite owner shadows coherently and proved
--
--   B_(Q+n) = B_Q 2^-n.
--
-- The inverse-limit suggestion becomes more useful analytically after writing
-- the exact telescope for the resource moved from the unresolved boundary
-- into the internal shells:
--
--   I_(Q+n) - I_Q = B_Q (1 - 2^-n).
--
-- Consequently
--
--   (I_(Q+n) - I_Q) + B_(Q+n) = B_Q.
--
-- Thus every finite refinement splits the old boundary fibre *exactly* into
-- resolved new-shell resource plus the new residual boundary.  This is the
-- finite projective identity the later Q -> infinity theorem must preserve;
-- no limiting convergence is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact as Budget
import DASHI.Physics.Closure.NSTriadKNShellBudgetProjectiveLedgerRound36Exact as Projective

internalAdvance : ℚ → Nat → Nat → ℚ
internalAdvance eta shell steps =
  Budget.internalBudget
    (Budget.canonicalFiniteShellBudgetGluing eta (shell + steps))
  - Budget.internalBudget
      (Budget.canonicalFiniteShellBudgetGluing eta shell)

internalAdvanceTelescope : ∀ eta shell steps →
  internalAdvance eta shell steps
  ≡
  Budget.boundaryBudget
    (Budget.canonicalFiniteShellBudgetGluing eta shell)
  * (1ℚ - Sharp.inverseDyadicScale steps)
internalAdvanceTelescope eta shell steps
  rewrite Budget.internalBudgetClosedForm eta (shell + steps)
        | Budget.internalBudgetClosedForm eta shell
        | Projective.inverseDyadicScaleAdd (suc shell) steps =
  solve
    ( eta
    ∷ Sharp.inverseDyadicScale (suc shell)
    ∷ Sharp.inverseDyadicScale steps
    ∷ [])

refinedBoundarySplitsOldBoundaryExactly : ∀ eta shell steps →
  internalAdvance eta shell steps
  + Budget.boundaryBudget
      (Budget.canonicalFiniteShellBudgetGluing eta (shell + steps))
  ≡ Budget.boundaryBudget
      (Budget.canonicalFiniteShellBudgetGluing eta shell)
refinedBoundarySplitsOldBoundaryExactly eta shell steps =
  trans
    (cong
      (λ advance →
        advance
        + Budget.boundaryBudget
            (Budget.canonicalFiniteShellBudgetGluing eta (shell + steps)))
      (internalAdvanceTelescope eta shell steps))
    (trans
      (cong
        (λ refinedBoundary →
          Budget.boundaryBudget
            (Budget.canonicalFiniteShellBudgetGluing eta shell)
          * (1ℚ - Sharp.inverseDyadicScale steps)
          + refinedBoundary)
        (Projective.boundaryBudgetAfterSteps eta shell steps))
      (solve
        ( Budget.boundaryBudget
            (Budget.canonicalFiniteShellBudgetGluing eta shell)
        ∷ Sharp.inverseDyadicScale steps
        ∷ [])))

oneStepInternalAdvanceIsTransferredGain : ∀ eta shell →
  internalAdvance eta shell (suc 0)
  ≡ Sharp.requiredHHBadGain eta (suc shell)
oneStepInternalAdvanceIsTransferredGain eta shell =
  Budget.internalBudgetIncrementIsNextGain eta shell

projectiveShellTelescopeClosed : Bool
projectiveShellTelescopeClosed = true

analyticBoundaryVanishingConstructed : Bool
analyticBoundaryVanishingConstructed = false

projectiveShellTelescopeClosedIsTrue :
  projectiveShellTelescopeClosed ≡ true
projectiveShellTelescopeClosedIsTrue = refl

analyticBoundaryVanishingConstructedIsFalse :
  analyticBoundaryVanishingConstructed ≡ false
analyticBoundaryVanishingConstructedIsFalse = refl
