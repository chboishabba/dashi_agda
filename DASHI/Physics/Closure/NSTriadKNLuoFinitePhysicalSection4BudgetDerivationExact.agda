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
j11LowerValue budgetData =
  Sum.sumTo
    (Prefix.j11Amplitude (shellL2 budgetData))
    (outputShell budgetData)

j11UpperValue : FinitePhysicalSection4BudgetData → ℚ
j11UpperValue budgetData = Jensen.sumValues (j11UpperSamples budgetData)

j12Value : FinitePhysicalSection4BudgetData → ℚ
j12Value budgetData = Jensen.sumValues (j12Samples budgetData)

j2Value : FinitePhysicalSection4BudgetData → ℚ
j2Value budgetData = Jensen.sumValues (j2Samples budgetData)

j11LowerBudget : FinitePhysicalSection4BudgetData → ℚ
j11LowerBudget budgetData =
  Prefix.lambda (outputShell budgetData)
  * Sum.sumTo
      (Prefix.j11EnergyDensity (shellL2 budgetData))
      (outputShell budgetData)

j11UpperBudgetTotal : FinitePhysicalSection4BudgetData → ℚ
j11UpperBudgetTotal budgetData =
  Jensen.rationalLength (j11UpperSamples budgetData)
  * sumBudget (j11UpperBudget budgetData) (j11UpperSamples budgetData)

j12BudgetTotal : FinitePhysicalSection4BudgetData → ℚ
j12BudgetTotal budgetData =
  Jensen.rationalLength (j12Samples budgetData)
  * sumBudget (j12Budget budgetData) (j12Samples budgetData)

j2BudgetTotal : FinitePhysicalSection4BudgetData → ℚ
j2BudgetTotal budgetData =
  Jensen.rationalLength (j2Samples budgetData)
  * sumBudget (j2Budget budgetData) (j2Samples budgetData)

physicalJ11LowerBound :
  (budgetData : FinitePhysicalSection4BudgetData) →
  L2.square (j11LowerValue budgetData) ≤ j11LowerBudget budgetData
physicalJ11LowerBound budgetData =
  Prefix.finiteJ11PrefixEnergyBound
    (shellL2 budgetData)
    (outputShell budgetData)

physicalJ11UpperBound :
  (budgetData : FinitePhysicalSection4BudgetData) →
  L2.square (j11UpperValue budgetData) ≤ j11UpperBudgetTotal budgetData
physicalJ11UpperBound budgetData =
  finiteSampleFoldBudget
    (j11UpperSamples budgetData)
    (j11UpperBudget budgetData)
    (j11UpperPointwise budgetData)

physicalJ12Bound :
  (budgetData : FinitePhysicalSection4BudgetData) →
  L2.square (j12Value budgetData) ≤ j12BudgetTotal budgetData
physicalJ12Bound budgetData =
  finiteSampleFoldBudget
    (j12Samples budgetData)
    (j12Budget budgetData)
    (j12Pointwise budgetData)

physicalJ2Bound :
  (budgetData : FinitePhysicalSection4BudgetData) →
  L2.square (j2Value budgetData) ≤ j2BudgetTotal budgetData
physicalJ2Bound budgetData =
  finiteSampleFoldBudget
    (j2Samples budgetData)
    (j2Budget budgetData)
    (j2Pointwise budgetData)

physicalJ11Bound :
  (budgetData : FinitePhysicalSection4BudgetData) →
  L2.square (j11LowerValue budgetData + j11UpperValue budgetData)
  ≤ Half.two
      * (j11LowerBudget budgetData + j11UpperBudgetTotal budgetData)
physicalJ11Bound budgetData =
  let
    splitSquare :
      L2.square (j11LowerValue budgetData + j11UpperValue budgetData)
      ≤ Half.two
        * ( L2.square (j11LowerValue budgetData)
          + L2.square (j11UpperValue budgetData))
    splitSquare =
      Half.squareOfSumBelowTwiceSquares
        (j11LowerValue budgetData)
        (j11UpperValue budgetData)

    component :
      L2.square (j11LowerValue budgetData)
        + L2.square (j11UpperValue budgetData)
      ≤ j11LowerBudget budgetData + j11UpperBudgetTotal budgetData
    component =
      ℚₚ.+-mono-≤
        (physicalJ11LowerBound budgetData)
        (physicalJ11UpperBound budgetData)

    scaled :
      Half.two
        * ( L2.square (j11LowerValue budgetData)
          + L2.square (j11UpperValue budgetData))
      ≤ Half.two
        * (j11LowerBudget budgetData + j11UpperBudgetTotal budgetData)
    scaled =
      let
        instance
          twoIsNonnegative = nonNegative Half.twoNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg Half.two component
  in
  ℚₚ.≤-trans splitSquare scaled

fourSection4SquareBoundsCombine :
  (budgetData : FinitePhysicalSection4BudgetData) →
  L2.square (j11LowerValue budgetData + j11UpperValue budgetData)
    + L2.square (j12Value budgetData)
    + L2.square (j2Value budgetData)
  ≤ Half.two
      * (j11LowerBudget budgetData + j11UpperBudgetTotal budgetData)
    + j12BudgetTotal budgetData
    + j2BudgetTotal budgetData
fourSection4SquareBoundsCombine budgetData =
  ℚₚ.+-mono-≤
    (ℚₚ.+-mono-≤
      (physicalJ11Bound budgetData)
      (physicalJ12Bound budgetData))
    (physicalJ2Bound budgetData)
