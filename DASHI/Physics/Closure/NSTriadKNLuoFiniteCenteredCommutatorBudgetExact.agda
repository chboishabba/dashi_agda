module DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Sum the quantitative remainder left by the exact paired Taylor
-- cancellation.  Each paired remainder is bounded by
--
--   secondMoment * curvature.
--
-- Nonnegative kernel weights are then used to derive
--
--   sum weight * remainder
--     <= curvature * sum weight * secondMoment.
--
-- This is the finite second-moment commutator budget.  It does not assume or
-- claim that the continuum Littlewood--Paley kernel has already been
-- instantiated.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

record CenteredRemainderSample : Set where
  constructor centered-remainder-sample
  field
    weight secondMoment remainderMagnitude : ℚ
    weightNonnegative : 0ℚ ≤ weight

open CenteredRemainderSample public

weightedRemainder : CenteredRemainderSample → ℚ
weightedRemainder sample =
  weight sample * remainderMagnitude sample

weightedSecondMoment : CenteredRemainderSample → ℚ
weightedSecondMoment sample =
  weight sample * secondMoment sample

sumBy :
  ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (sample ∷ samples) value =
  value sample + sumBy samples value

sumByMonotone :
  ∀ {A : Set}
    (samples : List A)
    (lower upper : A → ℚ) →
  ((sample : A) → lower sample ≤ upper sample) →
  sumBy samples lower ≤ sumBy samples upper
sumByMonotone [] lower upper pointwise = ℚₚ.≤-refl
sumByMonotone (sample ∷ samples) lower upper pointwise =
  ℚₚ.+-mono-≤
    (pointwise sample)
    (sumByMonotone samples lower upper pointwise)

sumByScaleLeft :
  ∀ {A : Set}
    (scale : ℚ)
    (samples : List A)
    (value : A → ℚ) →
  sumBy samples (λ sample → scale * value sample)
  ≡ scale * sumBy samples value
sumByScaleLeft scale [] value = solve (scale ∷ [])
sumByScaleLeft scale (sample ∷ samples) value
  rewrite sumByScaleLeft scale samples value =
  solve (scale ∷ value sample ∷ sumBy samples value ∷ [])

record FiniteCenteredCommutatorBudget : Set₁ where
  field
    samples : List CenteredRemainderSample
    curvature : ℚ

    pointwiseSecondMomentBound :
      (sample : CenteredRemainderSample) →
      remainderMagnitude sample ≤ secondMoment sample * curvature

open FiniteCenteredCommutatorBudget public

weightedPointwiseBound :
  (budget : FiniteCenteredCommutatorBudget) →
  (sample : CenteredRemainderSample) →
  weightedRemainder sample
  ≤ curvature budget * weightedSecondMoment sample
weightedPointwiseBound budget sample =
  let
    multiplied :
      weight sample * remainderMagnitude sample
      ≤ weight sample * (secondMoment sample * curvature budget)
    multiplied =
      let
        instance
          weightIsNonnegative = nonNegative (weightNonnegative sample)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (weight sample)
        (pointwiseSecondMomentBound budget sample)

    targetMeaning :
      weight sample * (secondMoment sample * curvature budget)
      ≡ curvature budget * weightedSecondMoment sample
    targetMeaning =
      solve
        ( weight sample
        ∷ secondMoment sample
        ∷ curvature budget
        ∷ []
        )
  in
  subst
    (λ upper → weightedRemainder sample ≤ upper)
    targetMeaning
    multiplied

finiteCenteredSecondMomentBudget :
  (budget : FiniteCenteredCommutatorBudget) →
  sumBy (samples budget) weightedRemainder
  ≤ curvature budget
      * sumBy (samples budget) weightedSecondMoment
finiteCenteredSecondMomentBudget budget =
  let
    pointwiseSum :
      sumBy (samples budget) weightedRemainder
      ≤ sumBy (samples budget)
          (λ sample → curvature budget * weightedSecondMoment sample)
    pointwiseSum =
      sumByMonotone
        (samples budget)
        weightedRemainder
        (λ sample → curvature budget * weightedSecondMoment sample)
        (weightedPointwiseBound budget)

    scaleMeaning :
      sumBy (samples budget)
        (λ sample → curvature budget * weightedSecondMoment sample)
      ≡ curvature budget
          * sumBy (samples budget) weightedSecondMoment
    scaleMeaning =
      sumByScaleLeft
        (curvature budget)
        (samples budget)
        weightedSecondMoment
  in
  subst
    (λ upper → sumBy (samples budget) weightedRemainder ≤ upper)
    scaleMeaning
    pointwiseSum
