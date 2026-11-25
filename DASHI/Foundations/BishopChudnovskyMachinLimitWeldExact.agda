module DASHI.Foundations.BishopChudnovskyMachinLimitWeldExact where

-- Source-written, NOT kernel checked. No new real, pi, or convergence axiom.
-- Consume the actual original Machin series, not a similarly named real.
-- The remaining input is a proof of the quantified error on the literal
-- embedded rational Chudnovsky approximants. Finite tests cannot supply it.

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_)
open import Data.Rational.Unnormalised using (ℚᵘ)
import Real as R
import Sequence as S
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as B
import DASHI.Analysis.BishopPolynomialSuccessorFactorLimitExact as C
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as V

sixteen four : R.ℝ
sixteen = R._⋆ M.sixteen
four = R._⋆ M.four

partial5 partial239 : Nat → R.ℝ
partial5 = S.SeriesOf (M.atanSignedTerm M.bishopOneFifth)
partial239 = S.SeriesOf (M.atanSignedTerm M.bishopOneTwoHundredThirtyNinth)

machinPartial : Nat → R.ℝ
machinPartial n =
  R._-_ (R._*_ sixteen (partial5 n)) (R._*_ four (partial239 n))

machinPartialConverges :
  S._ConvergesTo_ machinPartial M.bishopMachinPi
machinPartialConverges =
  S.xₙ+yₙ→x₀+y₀
    ( R._*_ sixteen M.bishopAtanOneFifth
    , S.xₙyₙ→x₀y₀
        (sixteen , C.constantSequenceConverges sixteen)
        (M.bishopAtanOneFifth ,
          M.bishopAtanHalfBallConverges M.bishopOneFifth
            M.bishopOneFifthInsideHalf))
    ( R.- (R._*_ four M.bishopAtanOneTwoHundredThirtyNinth)
    , S.-xₙ→-x₀
        ( R._*_ four M.bishopAtanOneTwoHundredThirtyNinth
        , S.xₙyₙ→x₀y₀
            (four , C.constantSequenceConverges four)
            (M.bishopAtanOneTwoHundredThirtyNinth ,
              M.bishopAtanHalfBallConverges
                M.bishopOneTwoHundredThirtyNinth
                M.bishopOneTwoHundredThirtyNinthInsideHalf)))

-- Quantified error consumer: 4/(n+1), or any already proved vanishing
-- error stream. Both arguments are on the original vendored carrier.
rationalApproximationConvergesToOriginalMachin :
  (candidate : Nat → ℚᵘ) →
  (error : Nat → R.ℝ) →
  S._ConvergesTo_ error R.0ℝ →
  (∀ n → R._≤_
    (R.∣ R._-_ (R._⋆ (candidate n)) (machinPartial n) ∣)
    (R.∣ error n ∣)) →
  S._ConvergesTo_ (λ n → R._⋆ (candidate n)) M.bishopMachinPi
rationalApproximationConvergesToOriginalMachin candidate error errorZero bound =
  V.vanishingDifferenceConvergence machinPartialConverges errorZero bound

rationalApproximationLimitIsOriginalMachin :
  (candidate : Nat → ℚᵘ) →
  (error : Nat → R.ℝ) →
  S._ConvergesTo_ error R.0ℝ →
  (∀ n → R._≤_
    (R.∣ R._-_ (R._⋆ (candidate n)) (machinPartial n) ∣)
    (R.∣ error n ∣)) →
  ∀ {limit : R.ℝ} →
  S._ConvergesTo_ (λ n → R._⋆ (candidate n)) limit →
  R._≃_ limit M.bishopMachinPi
rationalApproximationLimitIsOriginalMachin candidate error errorZero bound converges =
  S.uniqueness-of-limits converges
    (rationalApproximationConvergesToOriginalMachin candidate error errorZero bound)
