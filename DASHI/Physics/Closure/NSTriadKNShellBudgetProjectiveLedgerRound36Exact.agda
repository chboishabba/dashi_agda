module DASHI.Physics.Closure.NSTriadKNShellBudgetProjectiveLedgerRound36Exact where

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
-- Round 35 proved one-step cutoff gluing
--
--   I_Q + B_Q = eta,
--   B_(Q+1) = (1/2) B_Q.
--
-- This module turns those isolated steps into an exact coherent finite shadow
-- family.  The inverse dyadic factors form a multiplicative semigroup,
--
--   2^-(m+n) = 2^-m 2^-n,
--
-- so after n cutoff advances
--
--   B_(Q+n) = B_Q 2^-n.
--
-- Every finite shadow has exactly the same total owner resource eta.  This is
-- the algebraic projective-ledger structure needed by the later Q -> infinity
-- argument.  The actual analytic statement B_Q -> 0 and passage of physical
-- owner estimates to an infinite-shell limit remain separate open producers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadFiniteShellBudgetGluingRound35Exact as Budget

inverseDyadicScaleAdd :
  ∀ left right →
  Sharp.inverseDyadicScale (left + right)
  ≡ Sharp.inverseDyadicScale left * Sharp.inverseDyadicScale right
inverseDyadicScaleAdd zero right =
  ℚRing.solve-∀ (Sharp.inverseDyadicScale right)
inverseDyadicScaleAdd (suc left) right
  rewrite inverseDyadicScaleAdd left right =
  ℚRing.solve-∀
    Sharp.half
    (Sharp.inverseDyadicScale left)
    (Sharp.inverseDyadicScale right)

boundaryBudgetAfterSteps :
  ∀ eta lastShell steps →
  Budget.boundaryBudget
    (Budget.canonicalFiniteShellBudgetGluing eta (lastShell + steps))
  ≡
  Budget.boundaryBudget
    (Budget.canonicalFiniteShellBudgetGluing eta lastShell)
    * Sharp.inverseDyadicScale steps
boundaryBudgetAfterSteps eta lastShell steps =
  trans
    (cong
      (eta *_)
      (inverseDyadicScaleAdd (suc lastShell) steps))
    (ℚRing.solve-∀
      eta
      (Sharp.inverseDyadicScale (suc lastShell))
      (Sharp.inverseDyadicScale steps))

shadowTotal :
  ∀ eta shell → ℚ
shadowTotal eta shell =
  Budget.internalBudget (Budget.canonicalFiniteShellBudgetGluing eta shell)
  + Budget.boundaryBudget (Budget.canonicalFiniteShellBudgetGluing eta shell)

shadowTotalExact :
  ∀ eta shell → shadowTotal eta shell ≡ eta
shadowTotalExact eta shell =
  Budget.gluedBudgetExact
    (Budget.canonicalFiniteShellBudgetGluing eta shell)

shadowTotalsCoherent :
  ∀ eta coarse steps →
  shadowTotal eta (coarse + steps) ≡ shadowTotal eta coarse
shadowTotalsCoherent eta coarse steps =
  trans
    (shadowTotalExact eta (coarse + steps))
    (sym (shadowTotalExact eta coarse))
  where
  open import Relation.Binary.PropositionalEquality using (sym)

record CoherentShellBudgetLedger (eta : ℚ) : Set where
  constructor coherent-shell-budget-ledger
  field
    shadow : (shell : Nat) → Budget.FiniteShellBudgetGluing eta shell

    shadowCanonical :
      ∀ shell →
      shadow shell ≡ Budget.canonicalFiniteShellBudgetGluing eta shell

    oneStepTotalCoherence :
      ∀ shell →
      Budget.internalBudget (shadow (suc shell))
        + Budget.boundaryBudget (shadow (suc shell))
      ≡
      Budget.internalBudget (shadow shell)
        + Budget.boundaryBudget (shadow shell)

    boundaryOneStepHalves :
      ∀ shell →
      Budget.boundaryBudget (shadow (suc shell))
      ≡ Sharp.half * Budget.boundaryBudget (shadow shell)

open CoherentShellBudgetLedger public

canonicalCoherentShellBudgetLedger :
  ∀ eta → CoherentShellBudgetLedger eta
canonicalCoherentShellBudgetLedger eta =
  coherent-shell-budget-ledger
    (Budget.canonicalFiniteShellBudgetGluing eta)
    (λ shell → refl)
    (Budget.cutoffAdvanceConservesTotalBudget eta)
    (Budget.boundaryBudgetHalves eta)

canonicalLedgerBoundaryAfterSteps :
  ∀ eta shell steps →
  Budget.boundaryBudget
    (shadow (canonicalCoherentShellBudgetLedger eta) (shell + steps))
  ≡
  Budget.boundaryBudget
    (shadow (canonicalCoherentShellBudgetLedger eta) shell)
      * Sharp.inverseDyadicScale steps
canonicalLedgerBoundaryAfterSteps = boundaryBudgetAfterSteps

shellBudgetProjectiveLedgerClosed : Bool
shellBudgetProjectiveLedgerClosed = true

shellCutoffLimitPreservesOwnerLedgerConstructed : Bool
shellCutoffLimitPreservesOwnerLedgerConstructed = false

shellBudgetProjectiveLedgerClosedIsTrue :
  shellBudgetProjectiveLedgerClosed ≡ true
shellBudgetProjectiveLedgerClosedIsTrue = refl

shellCutoffLimitPreservesOwnerLedgerConstructedIsFalse :
  shellCutoffLimitPreservesOwnerLedgerConstructed ≡ false
shellCutoffLimitPreservesOwnerLedgerConstructedIsFalse = refl
