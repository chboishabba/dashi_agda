module DASHI.Physics.Closure.NSTriadKNLuoFinitePhysicalSection4BudgetDerivationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Derive four separate finite Section-4 budgets without accepting any final
-- J-bound as a field.  The lower J11 range is the literal dyadic prefix
--
--   sum_{r=0}^q lambda_r^2 u_r,
--
-- and is controlled by the proved source-shaped prefix inequality.  The
-- upper J11, J12, and J2 ranges are finite sample folds; pointwise square
-- majorants are summed and Jensen is then applied.  The two J11 ranges are
-- recombined only at the final (L+U)^2 <= 2(L^2+U^2) step.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJ11PrefixEnergyExact as Prefix
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSourceFaithfulSection4Exact as Source

sumBudget :
  (ℚ → ℚ) → List ℚ → ℚ
sumBudget budget [] = 0ℚ
sumBudget budget (value ∷ values) =
  budget value + sumBudget budget values

sumSquaresBelowPointwiseBudget :
  (budget : ℚ → ℚ) →
  (values : List ℚ) →
  ((value : ℚ) → L2.square value ≤ budget value) →
  Jensen.sumSquares values ≤ sumBudget budget values
sumSquaresBelowPointwiseBudget budget [] pointwise = ℚₚ.≤-refl
sumSquaresBelowPointwiseBudget budget (value ∷ values) pointwise =
  ℚₚ.+-mono-≤
    (pointwise value)
    (sumSquaresBelowPointwiseBudget budget values pointwise)

finiteSampleFoldBudget :
  (values : List ℚ) →
  (budget : ℚ → ℚ) →
  ((value : ℚ) → L2.square value ≤ budget value) →
  L2.square (Jensen.sumValues values)
  ≤ Jensen.rationalLength values * sumBudget budget values
finiteSampleFoldBudget values budget pointwise =
  Source.jensenWithEnergyBudget
    values
    (sumBudget budget values)
    (sumSquaresBelowPointwiseBudget budget values pointwise)

record FinitePhysicalSection4BudgetData : Set₁ where
  field
    outputShell : Nat
    shellL2 : Nat → ℚ

    j11UpperSamples j12Samples j2Samples : List ℚ

    j11UpperBudget j12Budget j2Budget : ℚ → ℚ

    j11UpperPointwise :
      (value : ℚ) → L2.square value ≤ j11UpperBudget value
    j12Pointwise :
      (value : ℚ) → L2.square value ≤ j12Budget value
    j2Pointwise :
      (value : ℚ) → L2.square value ≤ j2Budget value

open FinitePhysicalSection4BudgetData public

j11LowerValue : FinitePhysicalSection4BudgetData → ℚ
j11LowerValue data =
  Sum.sumTo
    (Prefix.j11Amplitude (shellL2 data))
    (outputShell data)

j11UpperValue : FinitePhysicalSection4BudgetData → ℚ
j11UpperValue data = Jensen.sumValues (j11UpperSamples data)

j12Value : FinitePhysicalSection4BudgetData → ℚ
j12Value data = Jensen.sumValues (j12Samples data)

j2Value : FinitePhysicalSection4BudgetData → ℚ
j2Value data = Jensen.sumValues (j2Samples data)

j11LowerBudget : FinitePhysicalSection4BudgetData → ℚ
j11LowerBudget data =
  Prefix.lambda (outputShell data)
  * Sum.sumTo
      (Prefix.j11EnergyDensity (shellL2 data))
      (outputShell data)

j11UpperBudgetTotal : FinitePhysicalSection4BudgetData → ℚ
j11UpperBudgetTotal data =
  Jensen.rationalLength (j11UpperSamples data)
  * sumBudget (j11UpperBudget data) (j11UpperSamples data)

j12BudgetTotal : FinitePhysicalSection4BudgetData → ℚ
j12BudgetTotal data =
  Jensen.rationalLength (j12Samples data)
  * sumBudget (j12Budget data) (j12Samples data)

j2BudgetTotal : FinitePhysicalSection4BudgetData → ℚ
j2BudgetTotal data =
  Jensen.rationalLength (j2Samples data)
  * sumBudget (j2Budget data) (j2Samples data)

physicalJ11LowerBound :
  (data : FinitePhysicalSection4BudgetData) →
  L2.square (j11LowerValue data) ≤ j11LowerBudget data
physicalJ11LowerBound data =
  Prefix.finiteJ11PrefixEnergyBound
    (shellL2 data)
    (outputShell data)

physicalJ11UpperBound :
  (data : FinitePhysicalSection4BudgetData) →
  L2.square (j11UpperValue data) ≤ j11UpperBudgetTotal data
physicalJ11UpperBound data =
  finiteSampleFoldBudget
    (j11UpperSamples data)
    (j11UpperBudget data)
    (j11UpperPointwise data)

physicalJ12Bound :
  (data : FinitePhysicalSection4BudgetData) →
  L2.square (j12Value data) ≤ j12BudgetTotal data
physicalJ12Bound data =
  finiteSampleFoldBudget
    (j12Samples data)
    (j12Budget data)
    (j12Pointwise data)

physicalJ2Bound :
  (data : FinitePhysicalSection4BudgetData) →
  L2.square (j2Value data) ≤ j2BudgetTotal data
physicalJ2Bound data =
  finiteSampleFoldBudget
    (j2Samples data)
    (j2Budget data)
    (j2Pointwise data)

physicalJ11Bound :
  (data : FinitePhysicalSection4BudgetData) →
  L2.square (j11LowerValue data + j11UpperValue data)
  ≤ Half.two
      * (j11LowerBudget data + j11UpperBudgetTotal data)
physicalJ11Bound data =
  let
    splitSquare :
      L2.square (j11LowerValue data + j11UpperValue data)
      ≤ Half.two
        * ( L2.square (j11LowerValue data)
          + L2.square (j11UpperValue data))
    splitSquare =
      Half.squareOfSumBelowTwiceSquares
        (j11LowerValue data)
        (j11UpperValue data)

    component :
      L2.square (j11LowerValue data)
        + L2.square (j11UpperValue data)
      ≤ j11LowerBudget data + j11UpperBudgetTotal data
    component =
      ℚₚ.+-mono-≤
        (physicalJ11LowerBound data)
        (physicalJ11UpperBound data)

    scaled :
      Half.two
        * ( L2.square (j11LowerValue data)
          + L2.square (j11UpperValue data))
      ≤ Half.two
        * (j11LowerBudget data + j11UpperBudgetTotal data)
    scaled =
      let instance twoIsNonnegative = nonNegative Half.twoNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg Half.two component
  in
  ℚₚ.≤-trans splitSquare scaled

fourSection4SquareBoundsCombine :
  (data : FinitePhysicalSection4BudgetData) →
  L2.square (j11LowerValue data + j11UpperValue data)
    + L2.square (j12Value data)
    + L2.square (j2Value data)
  ≤ Half.two
      * (j11LowerBudget data + j11UpperBudgetTotal data)
    + j12BudgetTotal data
    + j2BudgetTotal data
fourSection4SquareBoundsCombine data =
  ℚₚ.+-mono-≤
    (ℚₚ.+-mono-≤
      (physicalJ11Bound data)
      (physicalJ12Bound data))
    (physicalJ2Bound data)
