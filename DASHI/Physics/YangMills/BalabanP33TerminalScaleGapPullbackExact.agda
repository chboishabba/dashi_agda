module DASHI.Physics.YangMills.BalabanP33TerminalScaleGapPullbackExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence",
-- Annales Henri Poincare 15 (2014), 2133--2175.
-- DOI: 10.1007/s00023-013-0303-3.
--
-- J. Dimock,
-- "Ultraviolet Regularity for QED in d=3",
-- Journal of Mathematical Physics 59 (2018), 012301.
-- DOI: 10.1063/1.5009458.
--
-- DASHI CONTRIBUTION
--
-- Formalize the exact algebra that a terminal-scale spectral gap route must
-- discharge. No unproved physical scaling law such as m_{j+1}=2m_j is
-- asserted. Instead each RG step must provide the explicit inequality
--
--   m_{j+1} <= 2 m_j + epsilon_j.
--
-- It follows constructively that
--
--   (m_{j+1}-epsilon_j)/2 <= m_j.
--
-- Chaining N such steps gives a fine-scale lower floor obtained by repeatedly
-- halving the coarse floor and subtracting the corresponding loss. The module
-- proves the recursion and its closed exact-rational decomposition
--
--   2^{-N} m_N - sum_j 2^{-(j+1)} epsilon_j.
--
-- Round60 strengthens the earlier nonnegative budget criterion to the strict
-- form required by a physical mass gap:
--
--   discountedLossBudget < discountFactor(N) * terminalGap
--
-- implies BOTH
--
--   0 < pullBackGap terminalGap losses
--
-- and, for an actual GapTransferChain,
--
--   0 < fineGap.
--
-- The finite-volume terminal gap and every one-step physical estimate must be
-- proved elsewhere. Nothing here assumes a bare volume-uniform Poincare
-- constant or claims that RG dynamically generates a gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _<_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSZZStrongCouplingDecisionExact as SZZ

half : ℚ
half = + 1 / 2

two : ℚ
two = + 2 / 1

halfNonnegative : 0ℚ ≤ half
halfNonnegative = ℚP.nonNegative⁻¹ half

------------------------------------------------------------------------
-- One exact RG gap step.
------------------------------------------------------------------------

record GapTransferStep (fine coarse loss : ℚ) : Set where
  field
    coarseControlledByFine : coarse ≤ two * fine + loss

open GapTransferStep public

subtractRightMonotone : ∀ {left right} loss →
  left ≤ right → left - loss ≤ right - loss
subtractRightMonotone {left} {right} loss leftBelowRight =
  subst
    (λ lower → lower ≤ right - loss)
    (ℚRing.solve-∀ left loss)
    (subst
      (λ upper → left + (- loss) ≤ upper)
      (ℚRing.solve-∀ right loss)
      (ℚP.+-mono-≤ leftBelowRight ℚP.≤-refl))

multiplyHalfMonotone : ∀ {left right} →
  left ≤ right → half * left ≤ half * right
multiplyHalfMonotone {left} {right} leftBelowRight =
  let
    instance
      halfNN : NonNegative half
      halfNN = ℚ.nonNegative halfNonnegative

    rightScaled : left * half ≤ right * half
    rightScaled = ℚP.*-monoʳ-≤-nonNeg half leftBelowRight
  in
  subst
    (λ lower → lower ≤ half * right)
    (ℚRing.solve-∀ half left)
    (subst
      (λ upper → left * half ≤ upper)
      (ℚRing.solve-∀ half right)
      rightScaled)

halfSubtractMonotone : ∀ {left right} loss →
  left ≤ right →
  half * (left - loss) ≤ half * (right - loss)
halfSubtractMonotone loss leftBelowRight =
  multiplyHalfMonotone (subtractRightMonotone loss leftBelowRight)

oneStepPullbackLower : ∀ {fine coarse loss} →
  GapTransferStep fine coarse loss →
  half * (coarse - loss) ≤ fine
oneStepPullbackLower {fine} {coarse} {loss} step =
  let
    shifted : coarse - loss ≤ two * fine
    shifted =
      subst
        (λ upper → coarse - loss ≤ upper)
        (ℚRing.solve-∀ fine loss)
        (subtractRightMonotone loss
          (coarseControlledByFine step))

    halved : half * (coarse - loss) ≤ half * (two * fine)
    halved = multiplyHalfMonotone shifted
  in
  subst
    (λ upper → half * (coarse - loss) ≤ upper)
    (ℚRing.solve-∀ fine)
    halved

------------------------------------------------------------------------
-- A finite chain from the fine scale to a terminal coarse scale.
------------------------------------------------------------------------

data GapTransferChain : ℚ → List ℚ → ℚ → Set where
  terminal : ∀ gap → GapTransferChain gap [] gap
  step : ∀ {fine coarse terminalGap loss losses} →
    GapTransferStep fine coarse loss →
    GapTransferChain coarse losses terminalGap →
    GapTransferChain fine (loss ∷ losses) terminalGap

pullBackGap : ℚ → List ℚ → ℚ
pullBackGap terminalGap [] = terminalGap
pullBackGap terminalGap (loss ∷ losses) =
  half * (pullBackGap terminalGap losses - loss)

pullBackGapBelowFine : ∀ {fine losses terminalGap} →
  GapTransferChain fine losses terminalGap →
  pullBackGap terminalGap losses ≤ fine
pullBackGapBelowFine (terminal gap) = ℚP.≤-refl
pullBackGapBelowFine
    (step {fine} {coarse} {terminalGap} {loss} {losses}
      firstStep remainingSteps) =
  ℚP.≤-trans
    (halfSubtractMonotone loss
      (pullBackGapBelowFine remainingSteps))
    (oneStepPullbackLower firstStep)

------------------------------------------------------------------------
-- Closed discounted terminal-minus-loss form.
------------------------------------------------------------------------

discountFactor : Nat → ℚ
discountFactor zero = 1ℚ
discountFactor (suc n) = half * discountFactor n

discountedLossBudget : List ℚ → ℚ
discountedLossBudget [] = 0ℚ
discountedLossBudget (loss ∷ losses) =
  half * (discountedLossBudget losses + loss)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (value ∷ values) = suc (listLength values)

pullBackGapClosedForm : ∀ terminalGap losses →
  pullBackGap terminalGap losses
  ≡ discountFactor (listLength losses) * terminalGap
    - discountedLossBudget losses
pullBackGapClosedForm terminalGap [] =
  ℚRing.solve-∀ terminalGap
pullBackGapClosedForm terminalGap (loss ∷ losses)
  rewrite pullBackGapClosedForm terminalGap losses =
  ℚRing.solve-∀
    (discountFactor (listLength losses))
    terminalGap
    (discountedLossBudget losses)
    loss

fourStepPullbackExact : ∀ terminalGap loss0 loss1 loss2 loss3 →
  pullBackGap terminalGap (loss0 ∷ loss1 ∷ loss2 ∷ loss3 ∷ [])
  ≡ (+ 1 / 16) * terminalGap
    - ((+ 1 / 2) * loss0
      + (+ 1 / 4) * loss1
      + (+ 1 / 8) * loss2
      + (+ 1 / 16) * loss3)
fourStepPullbackExact terminalGap loss0 loss1 loss2 loss3 =
  ℚRing.solve-∀ terminalGap loss0 loss1 loss2 loss3

------------------------------------------------------------------------
-- Exact loss-budget criteria for nonnegative AND positive inherited floors.
------------------------------------------------------------------------

differenceNonnegative : ∀ {lower upper} →
  lower ≤ upper → 0ℚ ≤ upper - lower
differenceNonnegative {lower} {upper} lowerBelowUpper =
  subst
    (λ left → left ≤ upper - lower)
    (ℚRing.solve-∀ lower)
    (subtractRightMonotone lower lowerBelowUpper)

discountedLossBudgetAdmissible : ℚ → List ℚ → Set
discountedLossBudgetAdmissible terminalGap losses =
  discountedLossBudget losses
  ≤ discountFactor (listLength losses) * terminalGap

discountedLossBudgetStrictlyAdmissible : ℚ → List ℚ → Set
discountedLossBudgetStrictlyAdmissible terminalGap losses =
  discountedLossBudget losses
  < discountFactor (listLength losses) * terminalGap

admissibleBudgetImpliesPulledBackNonnegative :
  ∀ terminalGap losses →
  discountedLossBudgetAdmissible terminalGap losses →
  0ℚ ≤ pullBackGap terminalGap losses
admissibleBudgetImpliesPulledBackNonnegative
    terminalGap losses budgetAdmissible =
  subst
    (λ selected → 0ℚ ≤ selected)
    (sym (pullBackGapClosedForm terminalGap losses))
    (differenceNonnegative budgetAdmissible)

admissibleBudgetImpliesFineNonnegative :
  ∀ {fine losses terminalGap} →
  GapTransferChain fine losses terminalGap →
  discountedLossBudgetAdmissible terminalGap losses →
  0ℚ ≤ fine
admissibleBudgetImpliesFineNonnegative chain budgetAdmissible =
  ℚP.≤-trans
    (admissibleBudgetImpliesPulledBackNonnegative
      _ _ budgetAdmissible)
    (pullBackGapBelowFine chain)

strictBudgetImpliesPulledBackPositive :
  ∀ terminalGap losses →
  discountedLossBudgetStrictlyAdmissible terminalGap losses →
  0ℚ < pullBackGap terminalGap losses
strictBudgetImpliesPulledBackPositive
    terminalGap losses budgetStrict =
  subst
    (λ selected → 0ℚ < selected)
    (sym (pullBackGapClosedForm terminalGap losses))
    (SZZ.differencePositive
      (discountFactor (listLength losses) * terminalGap)
      (discountedLossBudget losses)
      budgetStrict)

strictBudgetImpliesFinePositive :
  ∀ {fine losses terminalGap} →
  GapTransferChain fine losses terminalGap →
  discountedLossBudgetStrictlyAdmissible terminalGap losses →
  0ℚ < fine
strictBudgetImpliesFinePositive chain budgetStrict =
  ℚP.<-≤-trans
    (strictBudgetImpliesPulledBackPositive _ _ budgetStrict)
    (pullBackGapBelowFine chain)

terminalGapPullbackStepLevel : ProofLevel
terminalGapPullbackStepLevel = machineChecked

terminalGapPullbackChainLevel : ProofLevel
terminalGapPullbackChainLevel = machineChecked

terminalGapDiscountedBudgetLevel : ProofLevel
terminalGapDiscountedBudgetLevel = machineChecked

terminalGapStrictDiscountedBudgetLevel : ProofLevel
terminalGapStrictDiscountedBudgetLevel = machineChecked

physicalRGGapTransferProducerLevel : ProofLevel
physicalRGGapTransferProducerLevel = conditional
