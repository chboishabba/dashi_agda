module DASHI.Foundations.BishopExponentialPositiveOrderExact where

------------------------------------------------------------------------
-- POSITIVE-SIDE ORDER LAWS FOR THE CONCRETE BISHOP EXPONENTIAL
--
-- These laws use only the concrete factorial series constructed in
-- BishopExponentialSeriesConvergenceExact and the order-limit theorems already
-- proved in the pinned Bishop Sequence.agda.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; 1ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
open import DASHI.Physics.YangMills.CompactLieProofLevel

expSeriesConvergent :
  (x : BishopReal.ℝ) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (Exp.expTerm x))
expSeriesConvergent x =
  BishopSequence.absolute⇒isConvergent
    (Exp.expAbsoluteSeriesConvergent x)

expTermZeroAtZero :
  BishopReal._≃_ (Exp.expTerm BishopReal.0ℝ zero) BishopReal.1ℝ
expTermZeroAtZero =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ 1ℚᵘ ⊗ Κ (+ 1 / 1)) ⊜ Κ 1ℚᵘ)
    BishopP.≃-refl

expTermZeroAtPositive :
  (n : Nat) →
  BishopReal._≃_
    (Exp.expTerm BishopReal.0ℝ (suc n))
    BishopReal.0ℝ
expTermZeroAtPositive n =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ oldPower coefficient →
      ((oldPower ⊗ Κ 0ℚᵘ) ⊗ coefficient) ⊜ Κ 0ℚᵘ)
    BishopP.≃-refl
    (BishopReal.pow BishopReal.0ℝ n)
    (Exp.embed (Exp.inverseFactorial (suc n)))

expZeroPartialSumPositive :
  (n : Nat) →
  BishopReal._≃_
    (BishopSequence.SeriesOf (Exp.expTerm BishopReal.0ℝ) (suc n))
    BishopReal.1ℝ
expZeroPartialSumPositive zero =
  BishopP.≃-trans
    (BishopP.+-cong BishopP.≃-refl expTermZeroAtZero)
    (BishopP.+-identityˡ BishopReal.1ℝ)
expZeroPartialSumPositive (suc n) =
  BishopP.≃-trans
    (BishopP.+-cong
      (expZeroPartialSumPositive n)
      (expTermZeroAtPositive n))
    (BishopP.+-identityʳ BishopReal.1ℝ)

bishopExpZero :
  BishopReal._≃_ (Exp.bishopExp BishopReal.0ℝ) BishopReal.1ℝ
bishopExpZero =
  BishopSequence.uniqueness-of-limits
    (Exp.bishopExpConverges BishopReal.0ℝ)
    (BishopSequence.xₙ≃c⇒xₙ→c
      (λ {(suc n) → expZeroPartialSumPositive n}))

expTermNonnegative :
  ∀ {x : BishopReal.ℝ} →
  BishopReal.NonNegative x →
  ∀ n → BishopReal.NonNegative (Exp.expTerm x n)
expTermNonnegative {x} xNonnegative n =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopSequence.nonNegx⇒nonNegxⁿ n xNonnegative)
    (Exp.embeddedInverseFactorialNonnegative n)

expPartialSumsIncreasing :
  ∀ {x : BishopReal.ℝ} →
  BishopReal.NonNegative x →
  BishopSequence._isIncreasing
    (BishopSequence.SeriesOf (Exp.expTerm x))
expPartialSumsIncreasing {x} xNonnegative n =
  let
    partial = BishopSequence.SeriesOf (Exp.expTerm x) n
    nextTerm = Exp.expTerm x n
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm (BishopP.+-identityʳ partial))
    (BishopP.+-monoʳ-≤ partial
      (BishopP.nonNegx⇒0≤x
        (expTermNonnegative xNonnegative n)))

expFirstTwoTerms :
  (x : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopSequence.SeriesOf (Exp.expTerm x) 2)
    (BishopReal._+_ BishopReal.1ℝ x)
expFirstTwoTerms x =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ →
      ((Κ 0ℚᵘ ⊕ (Κ 1ℚᵘ ⊗ Κ (+ 1 / 1)))
        ⊕ ((Κ 1ℚᵘ ⊗ x′) ⊗ Κ (+ 1 / 1)))
      ⊜ (Κ 1ℚᵘ ⊕ x′))
    BishopP.≃-refl x

oneBelowOnePlusPositive :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.1ℝ (BishopReal._+_ BishopReal.1ℝ x)
oneBelowOnePlusPositive {x} zeroBelowX =
  BishopP.<-respˡ-≃
    (BishopP.≃-symm (BishopP.+-identityʳ BishopReal.1ℝ))
    (BishopP.+-monoʳ-< BishopReal.1ℝ zeroBelowX)

bishopExpAtLeastOneOnNonnegative :
  ∀ {x : BishopReal.ℝ} →
  BishopReal.NonNegative x →
  BishopReal._≤_ BishopReal.1ℝ (Exp.bishopExp x)
bishopExpAtLeastOneOnNonnegative {x} xNonnegative =
  BishopP.≤-trans
    (BishopP.≤-reflexive
      (BishopP.≃-symm (expFirstTwoTerms x)))
    (BishopSequence.xₙisIncreasing⇒xₙ≤limxₙ
      (expPartialSumsIncreasing xNonnegative)
      (expSeriesConvergent x)
      2)
  |> BishopP.≤-respˡ-≃
      (BishopP.+-identityʳ BishopReal.1ℝ)
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  value |> f = f value

bishopExpStrictlyAboveOneOnPositive :
  ∀ {x : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.1ℝ (Exp.bishopExp x)
bishopExpStrictlyAboveOneOnPositive {x} zeroBelowX =
  BishopP.<-≤-trans
    (oneBelowOnePlusPositive zeroBelowX)
    (BishopP.≤-respˡ-≃
      (expFirstTwoTerms x)
      (BishopSequence.xₙisIncreasing⇒xₙ≤limxₙ
        (expPartialSumsIncreasing
          (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx zeroBelowX)))
        (expSeriesConvergent x)
        2))

bishopExponentialZeroLevel : ProofLevel
bishopExponentialZeroLevel = machineChecked

bishopExponentialPositiveSideOrderLevel : ProofLevel
bishopExponentialPositiveSideOrderLevel = machineChecked
