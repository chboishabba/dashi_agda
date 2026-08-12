module DASHI.Physics.Closure.NSTriadKNHHBadWeightedConjugationNoGoRound52Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- A tempting conjugation sets C~_q = w_q C_q, giving transformed inheritance
-- alpha~_q = alpha_q w_(q+1)/w_q.  Persistent improvement of alpha_q ~= 1
-- requires w_(q+1) <= rho w_q with rho < 1.  But the Clay-facing owner needs an
-- UNWEIGHTED C_q ceiling.  To recover that ceiling uniformly, w_q must stay
-- bounded below by one positive floor c.
--
-- Round 52 proves the finite-depth obstruction exactly:
--
--   c <= w_n <= rho^n w_0
--
-- for every n.  Hence any separately established shell n with rho^n w_0 < c
-- rules out the simultaneous claims "persistent contraction by weights" and
-- "uniform unweighted control".  We deliberately state the obstruction in this
-- finite rational form rather than importing exponential/Archimedean analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP

rationalPower : ℚ → Nat → ℚ
rationalPower rho zero = Data.Rational.Base.1ℚ
rationalPower rho (suc n) = rho * rationalPower rho n

record ConjugatingWeight : Set where
  field
    weight : Nat → ℚ
    rho : ℚ
    weightNonnegative : ∀ q → 0ℚ ≤ weight q
    rhoNonnegative : 0ℚ ≤ rho
    weightRatioBound : ∀ q → weight (suc q) ≤ rho * weight q

open ConjugatingWeight public

weightBelowGeometricEnvelope :
  (candidate : ConjugatingWeight) →
  ∀ n →
  weight candidate n
  ≤ rationalPower (rho candidate) n * weight candidate zero
weightBelowGeometricEnvelope candidate zero =
  ℚP.≤-refl
weightBelowGeometricEnvelope candidate (suc n) =
  let
    inherited :
      rho candidate * weight candidate n
      ≤ rho candidate
        * (rationalPower (rho candidate) n * weight candidate zero)
    inherited =
      let instance rhoNNI = nonNegative (rhoNonnegative candidate)
      in ℚP.*-monoˡ-≤-nonNeg
        (rho candidate)
        (weightBelowGeometricEnvelope candidate n)
  in
  ℚP.≤-trans
    (weightRatioBound candidate n)
    inherited

record UnweightedControlPreservingWeight
    (candidate : ConjugatingWeight) : Set where
  field
    lowerFloor : ℚ
    lowerFloorPositive : 0ℚ < lowerFloor
    lowerFloorBelowEveryWeight : ∀ q →
      lowerFloor ≤ weight candidate q

open UnweightedControlPreservingWeight public

positiveFloorBelowEveryGeometricEnvelope :
  ∀ {candidate}
    (control : UnweightedControlPreservingWeight candidate) n →
  lowerFloor control
  ≤ rationalPower (rho candidate) n * weight candidate zero
positiveFloorBelowEveryGeometricEnvelope {candidate} control n =
  ℚP.≤-trans
    (lowerFloorBelowEveryWeight control n)
    (weightBelowGeometricEnvelope candidate n)

record DeepShellGeometricCollapse
    (candidate : ConjugatingWeight)
    (control : UnweightedControlPreservingWeight candidate) : Set where
  field
    shell : Nat
    geometricEnvelopeBelowFloor :
      rationalPower (rho candidate) shell * weight candidate zero
      < lowerFloor control

open DeepShellGeometricCollapse public

weightedConjugationDeepShellContradiction :
  ∀ {candidate control} →
  DeepShellGeometricCollapse candidate control →
  lowerFloor control < lowerFloor control
weightedConjugationDeepShellContradiction {candidate} {control} collapse =
  ℚP.≤-<-trans
    (positiveFloorBelowEveryGeometricEnvelope control (shell collapse))
    (geometricEnvelopeBelowFloor collapse)

weightedConjugationCannotManufacturePersistentUnweightedContraction : Bool
weightedConjugationCannotManufacturePersistentUnweightedContraction = true

weightedConjugationNoGoIsFiniteAndDivisionFree : Bool
weightedConjugationNoGoIsFiniteAndDivisionFree = true

weightedConjugationCannotManufacturePersistentUnweightedContractionIsTrue :
  weightedConjugationCannotManufacturePersistentUnweightedContraction ≡ true
weightedConjugationCannotManufacturePersistentUnweightedContractionIsTrue = refl
