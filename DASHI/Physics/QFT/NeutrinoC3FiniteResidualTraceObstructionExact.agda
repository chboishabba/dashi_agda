module DASHI.Physics.QFT.NeutrinoC3FiniteResidualTraceObstructionExact where

------------------------------------------------------------------------
-- EXACT FINITE FLAVOUR-GROUP CLOSURE OBSTRUCTION FOR ONE RATIONAL U
--
-- Math roots:
-- Washington, Introduction to Cyclotomic Fields, 2nd ed. (1997):
--   ring of integers of Q(zeta3) is Z[zeta3].
-- Standard elementary result: finite-order complex matrix has
--   root-of-unity eigenvalues, hence algebraic-integer trace.
-- Model-theory root:
-- Fonseca & Grimus, JHEP 09 (2014) 033, finite residual groups.
--
-- This module computes the ACTUAL trace numerator for the preceding
-- post-hoc rational U and the same-lepton-space T*S generator.
-- It does NOT import or prove the full algebraic-integer implication:
-- applying that external theorem yields the mathematical corollary
-- that <T,S1> is INFINITE in this particular rational example.
-- This does NOT show that all finite flavour-group models fail.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤ᵇ_)
open import Data.Integer using (ℤ; +_; _-_)
open import Data.Empty using (⊥)

import DASHI.Physics.QFT.NeutrinoSameLeptonMassOperatorRationalExact as R
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Three
import DASHI.Reasoning.RelationalTernaryPhaseGeometry as E

------------------------------------------------------------------------
-- T = diag(1,zeta,zeta^2) on SAME flavour space.
-- S = M diag(1,-1,-1) M^T / D^2.
-- trace(T*S) in Q(zeta) is
--   [S_ee-S_tau_tau + (S_mu_mu-S_tau_tau)*zeta]/D^2.
-- ζ²=-1-ζ, so it reduces to the pair of rational coefficients.
------------------------------------------------------------------------

traceNumeratorA : ℤ
traceNumeratorA =
  R.residualNum R.firstInvolution Three.electron Three.electron
  - R.residualNum R.firstInvolution Three.tau Three.tau

traceNumeratorB : ℤ
traceNumeratorB =
  R.residualNum R.firstInvolution Three.muon Three.muon
  - R.residualNum R.firstInvolution Three.tau Three.tau

firstTraceCoefficientExact :
  traceNumeratorA ≡ + 213694885170400
firstTraceCoefficientExact = refl

secondTraceCoefficientExact :
  traceNumeratorB ≡ + 55365974464882
secondTraceCoefficientExact = refl

commonTraceDenominator : Nat
commonTraceDenominator = 181846007130841

-- Both rational coefficients are between consecutive integers.
-- In particular coefficientA in (1,2), coefficientB in (0,1).
traceAExceedsOne :
  (213694885170400 ≤ᵇ commonTraceDenominator) ≡ false
traceAExceedsOne = refl

traceALessThanTwo :
  (commonTraceDenominator * 2 ≤ᵇ 213694885170400) ≡ false
traceALessThanTwo = refl

traceBStrictlyPositive :
  (55365974464882 ≤ᵇ 0) ≡ false
traceBStrictlyPositive = refl

traceBLessThanOne :
  (commonTraceDenominator ≤ᵇ 55365974464882) ≡ false
traceBLessThanOne = refl

------------------------------------------------------------------------
-- Exact RING-NATIVE normalized-trace identity numerator.
-- This numerator is the actual Z[zeta] object; the denominator is
-- a separate positive integer D^2, not an arbitrary C3 phase.
------------------------------------------------------------------------

traceInEisensteinNumerator : E.EisensteinWave
traceInEisensteinNumerator =
  E.eisensteinWave traceNumeratorA traceNumeratorB

traceInEisensteinIsComputedPair :
  traceInEisensteinNumerator
    ≡ E.eisensteinWave
        (+ 213694885170400)
        (+ 55365974464882)
traceInEisensteinIsComputedPair = refl

------------------------------------------------------------------------
-- The NO-GO corollary stated in the roadmap additionally consumes
-- the standard external theorem:
--
--     finite order TS => tr(TS) algebraic integer
--     O_{Q(zeta)} = Z[zeta]
--     tr(TS)=a+b zeta, 1<a<2, 0<b<1
--     => tr(TS) not algebraic integer
--     => TS infinite order => <T,S1> infinite group.
--
-- These final algebraic-number-theory implications are intentionally
-- NOT asserted as Agda-kernel-proved until imported as actual theorems.
-- In particular, constructing residual elements after picking U
-- cannot be mistaken for a finite-group *prediction* of U.
------------------------------------------------------------------------

data FiniteGroupClosurePromotion : Set where

notPromotedWithoutAlgebraicIntegerTheorems :
  FiniteGroupClosurePromotion → ⊥
notPromotedWithoutAlgebraicIntegerTheorems ()
