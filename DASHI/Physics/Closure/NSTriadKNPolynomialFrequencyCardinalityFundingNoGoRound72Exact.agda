module DASHI.Physics.Closure.NSTriadKNPolynomialFrequencyCardinalityFundingNoGoRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND72 / POLYNOMIAL-FREQUENCY COUNTING NO-GO
--
-- A shell index j corresponds to physical frequency N=2^j.  Therefore a
-- polynomial cardinality N^d is exponential in j.  If the Round71 finite
-- Cauchy lower bound loses the reciprocal of that cardinality, then even a
-- scale-independent remainder produces geometric shell floors.
--
-- This file formalises the two optimistic baselines discussed in Round72:
--
--   d=2 : floor_j = 2^(-2j),
--   d=3 : floor_j = 2^(-3j).
--
-- Both are pointwise below the already-proved dyadic sequence 2^(-j), whose
-- every finite prefix is <=2.  Hence every finite d=2 or d=3 prefix admits an
-- explicit Round70 funded event ledger under the single finite budget E=2.
--
-- CONSEQUENCE: proving only O(N^2) or O(N^3) raw lattice complexity cannot
-- close the finite-funding contradiction.  A viable route needs additional
-- multiplicity, a slower effective-complexity loss, or factorized/energy-
-- controlled Cauchy weights.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNHHGoodFourthOrderDyadicL1Round62Exact as Dyadic
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding

halfBelowOne : Scale.half ≤ 1ℚ
halfBelowOne = toWitness {a? = Scale.half ≤? 1ℚ} _

inverseDyadicScaleBelowOne : ∀ n → Scale.inverseDyadicScale n ≤ 1ℚ
inverseDyadicScaleBelowOne zero = ℚP.≤-refl
inverseDyadicScaleBelowOne (suc n) =
  let
    d = Scale.inverseDyadicScale n
    productBound : Scale.half * d ≤ 1ℚ * 1ℚ
    productBound =
      L2.nonnegativeProductMonotone
        Dyadic.halfNonnegative
        (Dyadic.inverseDyadicScaleNonnegative n)
        ℚP.0≤1 ℚP.0≤1
        halfBelowOne
        (inverseDyadicScaleBelowOne n)
  in
  subst (Scale.inverseDyadicScale (suc n) ≤_)
    (ℚP.*-identityˡ 1ℚ)
    productBound

quadraticFrequencyFloor : Nat → ℚ
quadraticFrequencyFloor n =
  L2.square (Scale.inverseDyadicScale n)

cubicFrequencyFloor : Nat → ℚ
cubicFrequencyFloor n =
  quadraticFrequencyFloor n * Scale.inverseDyadicScale n

quadraticFloorNonnegative : ∀ n → 0ℚ ≤ quadraticFrequencyFloor n
quadraticFloorNonnegative n = L2.squareNonnegative (Scale.inverseDyadicScale n)

cubicFloorNonnegative : ∀ n → 0ℚ ≤ cubicFrequencyFloor n
cubicFloorNonnegative n =
  let
    qNN = quadraticFloorNonnegative n
    dNN = Dyadic.inverseDyadicScaleNonnegative n
    instance
      qNNI = nonNegative qNN
      dNNI = nonNegative dNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (quadraticFrequencyFloor n) (Scale.inverseDyadicScale n)
  in ℚP.nonNegative⁻¹ (cubicFrequencyFloor n)

quadraticFloorBelowDyadic : ∀ n →
  quadraticFrequencyFloor n ≤ Scale.inverseDyadicScale n
quadraticFloorBelowDyadic n =
  let
    d = Scale.inverseDyadicScale n
    base : d * d ≤ d * 1ℚ
    base =
      L2.nonnegativeProductMonotone
        (Dyadic.inverseDyadicScaleNonnegative n)
        (Dyadic.inverseDyadicScaleNonnegative n)
        (Dyadic.inverseDyadicScaleNonnegative n)
        ℚP.0≤1
        ℚP.≤-refl
        (inverseDyadicScaleBelowOne n)
  in
  subst (quadraticFrequencyFloor n ≤_)
    (ℚP.*-identityʳ d)
    base

cubicFloorBelowQuadratic : ∀ n →
  cubicFrequencyFloor n ≤ quadraticFrequencyFloor n
cubicFloorBelowQuadratic n =
  let
    q = quadraticFrequencyFloor n
    d = Scale.inverseDyadicScale n
    base : q * d ≤ q * 1ℚ
    base =
      L2.nonnegativeProductMonotone
        (quadraticFloorNonnegative n)
        (Dyadic.inverseDyadicScaleNonnegative n)
        (quadraticFloorNonnegative n)
        ℚP.0≤1
        ℚP.≤-refl
        (inverseDyadicScaleBelowOne n)
  in
  subst (cubicFrequencyFloor n ≤_)
    (ℚP.*-identityʳ q)
    base

floorPrefix : (Nat → ℚ) → Nat → List ℚ
floorPrefix floor zero = floor zero ∷ []
floorPrefix floor (suc n) = floor (suc n) ∷ floorPrefix floor n

prefixSum : (Nat → ℚ) → Nat → ℚ
prefixSum floor n = Funding.sumFloors (floorPrefix floor n)

prefixPointwiseComparison :
  ∀ {left right} →
  (∀ n → left n ≤ right n) →
  ∀ n → prefixSum left n ≤ prefixSum right n
prefixPointwiseComparison compare zero =
  ℚP.+-mono-≤ (compare zero) ℚP.≤-refl
prefixPointwiseComparison compare (suc n) =
  ℚP.+-mono-≤ (compare (suc n))
    (prefixPointwiseComparison compare n)

dyadicPrefixSumExact : ∀ n →
  prefixSum Scale.inverseDyadicScale n ≡ Dyadic.partialDyadicWeight n
dyadicPrefixSumExact zero = solve []
dyadicPrefixSumExact (suc n)
  rewrite dyadicPrefixSumExact n =
  solve
    ( Scale.inverseDyadicScale (suc n)
    ∷ Dyadic.partialDyadicWeight n
    ∷ [])

dyadicPrefixBelowTwo : ∀ n →
  prefixSum Scale.inverseDyadicScale n ≤ Scale.two
dyadicPrefixBelowTwo n =
  subst (_≤ Scale.two)
    (sym (dyadicPrefixSumExact n))
    (Dyadic.partialDyadicWeightBelowTwo n)

quadraticPrefixBelowTwo : ∀ n →
  prefixSum quadraticFrequencyFloor n ≤ Scale.two
quadraticPrefixBelowTwo n =
  ℚP.≤-trans
    (prefixPointwiseComparison quadraticFloorBelowDyadic n)
    (dyadicPrefixBelowTwo n)

cubicPrefixBelowTwo : ∀ n →
  prefixSum cubicFrequencyFloor n ≤ Scale.two
cubicPrefixBelowTwo n =
  ℚP.≤-trans
    (prefixPointwiseComparison
      (λ shell → ℚP.≤-trans
        (cubicFloorBelowQuadratic shell)
        (quadraticFloorBelowDyadic shell)) n)
    (dyadicPrefixBelowTwo n)

allQuadraticFloorsNonnegative : ∀ n →
  Funding.AllFloorsNonnegative (floorPrefix quadraticFrequencyFloor n)
allQuadraticFloorsNonnegative zero =
  Funding.nonnegative∷ (quadraticFloorNonnegative zero)
    Funding.nonnegative[]
allQuadraticFloorsNonnegative (suc n) =
  Funding.nonnegative∷ (quadraticFloorNonnegative (suc n))
    (allQuadraticFloorsNonnegative n)

allCubicFloorsNonnegative : ∀ n →
  Funding.AllFloorsNonnegative (floorPrefix cubicFrequencyFloor n)
allCubicFloorsNonnegative zero =
  Funding.nonnegative∷ (cubicFloorNonnegative zero)
    Funding.nonnegative[]
allCubicFloorsNonnegative (suc n) =
  Funding.nonnegative∷ (cubicFloorNonnegative (suc n))
    (allCubicFloorsNonnegative n)

quadraticFrequencyEveryFinitePrefixFundedByTwo : ∀ n →
  Funding.ScaleDependentConcentrationBudget
    Scale.two
    (floorPrefix quadraticFrequencyFloor n)
    (Funding.exactFloorEvents
      (floorPrefix quadraticFrequencyFloor n)
      (allQuadraticFloorsNonnegative n))
quadraticFrequencyEveryFinitePrefixFundedByTwo n =
  Funding.summableFloorsAdmitFundedLedger
    (allQuadraticFloorsNonnegative n)
    (quadraticPrefixBelowTwo n)

cubicFrequencyEveryFinitePrefixFundedByTwo : ∀ n →
  Funding.ScaleDependentConcentrationBudget
    Scale.two
    (floorPrefix cubicFrequencyFloor n)
    (Funding.exactFloorEvents
      (floorPrefix cubicFrequencyFloor n)
      (allCubicFloorsNonnegative n))
cubicFrequencyEveryFinitePrefixFundedByTwo n =
  Funding.summableFloorsAdmitFundedLedger
    (allCubicFloorsNonnegative n)
    (cubicPrefixBelowTwo n)

round72QuadraticFrequencyCountingAloneClosesFunding : Bool
round72QuadraticFrequencyCountingAloneClosesFunding = false

round72CubicFrequencyCountingAloneClosesFunding : Bool
round72CubicFrequencyCountingAloneClosesFunding = false

round72PolynomialFrequencyCountingFundingNoGoConstructed : Bool
round72PolynomialFrequencyCountingFundingNoGoConstructed = true

round72PolynomialFrequencyCountingFundingNoGoConstructedIsTrue :
  round72PolynomialFrequencyCountingFundingNoGoConstructed ≡ true
round72PolynomialFrequencyCountingFundingNoGoConstructedIsTrue = refl
