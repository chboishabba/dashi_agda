module DASHI.Biology.BH4PNPEnergyBudgetCompositionExact where

-- Abstract, exact Nat-valued energy-budget composition.
-- This is an accounting theorem, NOT a numerical or physical entropy
-- certificate for the original 29x12 Rhea PNP system.
--
-- Attribution: implementation assistance to the existing BH4/369
-- programme. The additive energy-accounting principle is elementary
-- prior mathematics. No measurement, original kinetics or boundary
-- selection is introduced by this file.

open import DASHI.Core.Prelude

-- A receipt pays for every change in one common nonnegative energy
-- accounting unit. "credit" includes any *explicitly justified*
-- exterior work and numerical-residual allowance; "loss" includes
-- dissipated energy and convexity remainder.
record EnergyBudgetStep (initial final : Nat) : Set where
  constructor energy-budget-step
  field
    loss credit : Nat
    exactBudget : final + loss ≡ initial + credit

open EnergyBudgetStep public

-- Rearranging the last two additions, with no cancellation assumptions.
exchangeRight : (a b c : Nat) → a + (b + c) ≡ (a + c) + b
exchangeRight a b c =
  trans
    (cong (λ x → a + x) (+-comm b c))
    (sym (+-assoc a c b))

exchangeAdjacent : (a b c : Nat) → (a + b) + c ≡ (a + c) + b
exchangeAdjacent a b c =
  trans (+-assoc a b c) (exchangeRight a b c)

-- The same intermediate physical state is shared by the receipts.
-- This is why the type uses [initial, middle] and [middle, final],
-- rather than joining unrelated models with the same vector length.
composeEnergyBudget :
  ∀ {initial middle final} →
  EnergyBudgetStep initial middle →
  EnergyBudgetStep middle final →
  EnergyBudgetStep initial final
composeEnergyBudget {initial} {middle} {final} first second =
  energy-budget-step
    (loss first + loss second)
    (credit first + credit second)
    (trans
      (exchangeRight final (loss first) (loss second))
      (trans
        (cong (λ x → x + loss first) (exactBudget second))
        (trans
          (exchangeAdjacent middle (credit second) (loss first))
          (trans
            (cong (λ x → x + credit second) (exactBudget first))
            (+-assoc initial (credit first) (credit second))))))

-- A nonempty chronological history, indexed by the exact start/end
-- energies of adjacent receipts. No phantom idle step is introduced.
data EnergyBudgetHistory : Nat → Nat → Set where
  one : ∀ {initial final} →
    EnergyBudgetStep initial final →
    EnergyBudgetHistory initial final
  followedBy : ∀ {initial middle final} →
    EnergyBudgetStep initial middle →
    EnergyBudgetHistory middle final →
    EnergyBudgetHistory initial final

-- General exact ledger for arbitrary finite histories.
allStepsEnergyBudgetExact :
  ∀ {initial final} →
  EnergyBudgetHistory initial final →
  EnergyBudgetStep initial final
allStepsEnergyBudgetExact (one step) = step
allStepsEnergyBudgetExact (followedBy step rest) =
  composeEnergyBudget step (allStepsEnergyBudgetExact rest)

-- The source/solver may independently pay exact zero credit.
-- A free nonnegative loss then gives an explicit budget witness:
-- final + loss = initial. This is stronger than a numerical decrease
-- heuristic and never assumes the original physics is dissipative.
zeroCreditHistoryHasExactLossWitness :
  ∀ {initial final}
  (history : EnergyBudgetHistory initial final) →
  credit (allStepsEnergyBudgetExact history) ≡ 0 →
  final + loss (allStepsEnergyBudgetExact history) ≡ initial
zeroCreditHistoryHasExactLossWitness {initial} history zeroCredit =
  trans
    (exactBudget (allStepsEnergyBudgetExact history))
    (trans
      (cong (λ x → initial + x) zeroCredit)
      (+-identityʳ initial))


------------------------------------------------------------------------
-- Order-theoretic extraction: an exact budget really bounds final energy.
-- This proof does not assume that all credit is zero.
------------------------------------------------------------------------

initialBelowInitialPlus : (a b : Nat) → a ≤ a + b
initialBelowInitialPlus zero b = z≤n
initialBelowInitialPlus (suc a) b =
  s≤s (initialBelowInitialPlus a b)

stepFinalBoundedByInitialAndCredit :
  ∀ {initial final} (step : EnergyBudgetStep initial final) →
  final ≤ initial + credit step
stepFinalBoundedByInitialAndCredit {final = final} step =
  subst (λ x → final ≤ x)
    (exactBudget step)
    (initialBelowInitialPlus final (loss step))

allStepsFinalBoundedByInitialAndCredit :
  ∀ {initial final} (history : EnergyBudgetHistory initial final) →
  final ≤ initial + credit (allStepsEnergyBudgetExact history)
allStepsFinalBoundedByInitialAndCredit history =
  stepFinalBoundedByInitialAndCredit
    (allStepsEnergyBudgetExact history)

zeroCreditHistoryNonincreasing :
  ∀ {initial final} (history : EnergyBudgetHistory initial final) →
  credit (allStepsEnergyBudgetExact history) ≡ 0 →
  final ≤ initial
zeroCreditHistoryNonincreasing {initial} {final} history zeroCredit =
  subst (λ x → final ≤ x)
    (trans
      (cong (λ x → initial + x) zeroCredit)
      (+-identityʳ initial))
    (allStepsFinalBoundedByInitialAndCredit history)

-- Counterexample to any claim that an unqualified positive-credit step
-- must decrease: energy can increase if work/residual credits pay for it.
positiveCreditCanIncreaseEnergy : EnergyBudgetStep 0 1
positiveCreditCanIncreaseEnergy = energy-budget-step 0 1 refl
