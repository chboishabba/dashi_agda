module DASHI.Physics.Closure.NSCompactGammaFiveHalvesSummationReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaGeometricShellDecay as Geometric

------------------------------------------------------------------------
-- Correct countable-summation cut for the weighted five-halves theorem.
--
-- The shellwise estimate is multiplicative:
--
--   A_j <= c_{j,K} * E_Gamma(K,u),
--
-- and the coefficient family is summable uniformly in K.  This avoids summing a
-- full unweighted envelope once for every shell.  Countable monotonicity and the
-- factorization of the constant envelope are explicit analytic laws.
------------------------------------------------------------------------

record CountableNonnegativeShellSummation
    {i : Level}
    (A : AbsorptionArithmetic)
    (M : Geometric.OrderedSemiringExtension A)
    (Shell : Set i) : Set (lsuc i) where
  field
    sum : (Shell → Scalar A) → Scalar A

    sumMonotone : ∀ {f g} →
      (∀ j → _≤_ A (f j) (g j)) →
      _≤_ A (sum f) (sum g)

    factorConstantRight : ∀ coefficient envelope →
      sum (λ j → Geometric._*_ M (coefficient j) envelope) ≡
      Geometric._*_ M (sum coefficient) envelope

open CountableNonnegativeShellSummation public

record FiveHalvesPointwiseSummationInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Shell Time State : Set i

    multiplicativeOrder : Geometric.OrderedSemiringExtension A
    summation :
      CountableNonnegativeShellSummation A multiplicativeOrder Shell

    selectedState : Index → Time → State

    weightedFiveHalvesShell : Shell → State → Scalar A
    shellCoefficient : Index → Shell → Scalar A
    rawCompactGammaEnvelope : Index → Time → Scalar A

    coefficientSumBound displayedCompactGammaEnvelope :
      Index → Time → Scalar A

    pointwiseFiveHalvesDecay : ∀ q j τ →
      _≤_ A
        (weightedFiveHalvesShell j (selectedState q τ))
        (Geometric._*_ multiplicativeOrder
          (shellCoefficient q j)
          (rawCompactGammaEnvelope q τ))

    shellCoefficientSummable : ∀ q τ →
      _≤_ A
        (sum summation (shellCoefficient q))
        (coefficientSumBound q τ)

    normalizedCoefficientTimesEnvelopeFits : ∀ q τ →
      _≤_ A
        (Geometric._*_ multiplicativeOrder
          (coefficientSumBound q τ)
          (rawCompactGammaEnvelope q τ))
        (displayedCompactGammaEnvelope q τ)

open FiveHalvesPointwiseSummationInputs public

weightedFiveHalvesSum :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  FiveHalvesPointwiseSummationInputs A Index →
  Index → FiveHalvesPointwiseSummationInputs.Time → Scalar A
weightedFiveHalvesSum P q τ =
  sum (summation P)
    (λ j → weightedFiveHalvesShell P j (selectedState P q τ))

pointwiseDecaySumsToRawEnvelope :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (P : FiveHalvesPointwiseSummationInputs A Index) → ∀ q τ →
  _≤_ A
    (weightedFiveHalvesSum P q τ)
    (Geometric._*_ (multiplicativeOrder P)
      (sum (summation P) (shellCoefficient P q))
      (rawCompactGammaEnvelope P q τ))
pointwiseDecaySumsToRawEnvelope {A = A} P q τ =
  subst
    (λ upper → _≤_ A (weightedFiveHalvesSum P q τ) upper)
    (factorConstantRight
      (summation P)
      (shellCoefficient P q)
      (rawCompactGammaEnvelope P q τ))
    (sumMonotone (summation P)
      (λ j → pointwiseFiveHalvesDecay P q j τ))

fiveHalvesSumBelowDisplayedEnvelope :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (P : FiveHalvesPointwiseSummationInputs A Index) → ∀ q τ →
  _≤_ A
    (weightedFiveHalvesSum P q τ)
    (displayedCompactGammaEnvelope P q τ)
fiveHalvesSumBelowDisplayedEnvelope {A = A} P q τ =
  ≤-trans A
    (pointwiseDecaySumsToRawEnvelope P q τ)
    (≤-trans A
      (Geometric.multiplicationMonotoneLeft
        (multiplicativeOrder P)
        (rawCompactGammaEnvelope P q τ)
        (shellCoefficientSummable P q τ))
      (normalizedCoefficientTimesEnvelopeFits P q τ))
