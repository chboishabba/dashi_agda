module DASHI.Biology.BH4PNPSeparatedEnergyLedgerExact where

-- P0.06 mathematical energy-ledger decomposition for sequential steps.
-- The four Nat values are abstract nonnegative accounting units, NOT
-- physical entropy, original measured rates or certified rounding.
-- In particular, neither an exterior-work nor a residual allowance may
-- be set to zero without an independently supplied zero witness.
--
-- Attribution: elementary additive algebra, implemented as assistance
-- over the pre-existing DASHI BH4/369 programme and its original geometry.

open import DASHI.Core.Prelude
import DASHI.Biology.BH4PNPEnergyBudgetCompositionExact as Budget

record SeparatedEnergyStep (initial final : Nat) : Set where
  constructor separated-energy-step
  field
    transportAndReactionDissipation : Nat
    convexityRemainder : Nat
    numericalResidualAllowance : Nat
    exteriorWorkAllowance : Nat
    exactSeparatedLedger :
      final + (transportAndReactionDissipation + convexityRemainder)
        ≡ initial + (numericalResidualAllowance + exteriorWorkAllowance)

open SeparatedEnergyStep public

toEnergyBudget :
  ∀ {initial final} →
  SeparatedEnergyStep initial final →
  Budget.EnergyBudgetStep initial final
toEnergyBudget step =
  Budget.energy-budget-step
    (transportAndReactionDissipation step + convexityRemainder step)
    (numericalResidualAllowance step + exteriorWorkAllowance step)
    (exactSeparatedLedger step)

-- Shuffle additive pairs while retaining distinct physical/evidence
-- categories, rather than merging exterior work into a hidden sink.
pairRegroup :
  (a b c d : Nat) →
  (a + b) + (c + d) ≡ (a + c) + (b + d)
pairRegroup a b c d =
  trans
    (sym (+-assoc (a + b) c d))
    (trans
      (cong (λ x → x + d) (Budget.exchangeAdjacent a b c))
      (+-assoc (a + c) b d))

composeSeparatedEnergy :
  ∀ {initial middle final} →
  SeparatedEnergyStep initial middle →
  SeparatedEnergyStep middle final →
  SeparatedEnergyStep initial final
composeSeparatedEnergy {initial} {final = final} first second =
  separated-energy-step
    (transportAndReactionDissipation first
      + transportAndReactionDissipation second)
    (convexityRemainder first + convexityRemainder second)
    (numericalResidualAllowance first
      + numericalResidualAllowance second)
    (exteriorWorkAllowance first + exteriorWorkAllowance second)
    (trans
      (cong (λ x → final + x)
        (sym (pairRegroup
          (transportAndReactionDissipation first)
          (convexityRemainder first)
          (transportAndReactionDissipation second)
          (convexityRemainder second))))
      (trans
        (Budget.exactBudget
          (Budget.composeEnergyBudget
            (toEnergyBudget first) (toEnergyBudget second)))
        (cong (λ x → initial + x)
          (pairRegroup
            (numericalResidualAllowance first)
            (exteriorWorkAllowance first)
            (numericalResidualAllowance second)
            (exteriorWorkAllowance second)))))

data SeparatedEnergyHistory : Nat → Nat → Set where
  one : ∀ {initial final} →
    SeparatedEnergyStep initial final →
    SeparatedEnergyHistory initial final
  followedBy : ∀ {initial middle final} →
    SeparatedEnergyStep initial middle →
    SeparatedEnergyHistory middle final →
    SeparatedEnergyHistory initial final

allSeparatedStepsExact :
  ∀ {initial final} →
  SeparatedEnergyHistory initial final →
  SeparatedEnergyStep initial final
allSeparatedStepsExact (one step) = step
allSeparatedStepsExact (followedBy step rest) =
  composeSeparatedEnergy step (allSeparatedStepsExact rest)

allSeparatedStepsFinalBound :
  ∀ {initial final} (history : SeparatedEnergyHistory initial final) →
  final ≤ initial
    + (numericalResidualAllowance (allSeparatedStepsExact history)
      + exteriorWorkAllowance (allSeparatedStepsExact history))
allSeparatedStepsFinalBound history =
  Budget.stepFinalBoundedByInitialAndCredit
    (toEnergyBudget (allSeparatedStepsExact history))

-- The two credit categories each need their own zero evidence.
-- No assumption is made that closed-domain conditions or exact numerical
-- roots actually hold for the original BH4/369 PNP evolution.
noResidualNoExteriorWorkHistoryNonincreasing :
  ∀ {initial final} (history : SeparatedEnergyHistory initial final) →
  numericalResidualAllowance (allSeparatedStepsExact history) ≡ 0 →
  exteriorWorkAllowance (allSeparatedStepsExact history) ≡ 0 →
  final ≤ initial
noResidualNoExteriorWorkHistoryNonincreasing history residualZero exteriorZero =
  Budget.zeroCreditHistoryNonincreasing
    (Budget.one (toEnergyBudget (allSeparatedStepsExact history)))
    (trans (cong₂ _+_ residualZero exteriorZero) refl)

-- Counterexample: without a paid external-work/solver-residual zero
-- witness, a step may increase its energy. This is an explicit
-- safeguard against misapplying the closed-system theorem.
positiveExteriorWorkCanIncreaseEnergy : SeparatedEnergyStep 0 1
positiveExteriorWorkCanIncreaseEnergy =
  separated-energy-step 0 0 0 1 refl
