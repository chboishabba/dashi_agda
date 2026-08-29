module DASHI.Foundations.BishopNatSquareRootPositiveExact where

------------------------------------------------------------------------
-- STRICT POSITIVITY OF THE CONSTRUCTED NAT SQUARE ROOT
--
-- For 1 <= N it is enough, by Bishop's Positive constructor, to exhibit one
-- sequence precision p with a_p(N) > 1/p.  We use p=2.
--
-- Since 4 <= 4N, candidate 2 is admitted by the finite floor-root search, so
--
--   2 <= floorSquareRoot(4N),
--
-- hence a_2(N) >= 1 > 1/2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base as ℤ using (+_; +<+)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; con; _:=_)
open import Data.Rational.Unnormalised as ℚ using (_/_; _≤_; _<_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import Real as BishopReal
import RealProperties as BishopP
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as FloorApprox
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fraction
open import DASHI.Physics.YangMills.CompactLieProofLevel

two : Nat
two = suc (suc zero)

four : Nat
four = two * two

scaledAtTwoNormalForm :
  (radicand : Nat) →
  radicand * four ≡ FloorApprox.scaledSquareTarget radicand two
scaledAtTwoNormalForm =
  solve 1
    (λ n → n :* con 4 := (n :* con 2) :* con 2)
    refl

fourBelowScaledTargetAtTwo :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  four ≤ FloorApprox.scaledSquareTarget radicand two
fourBelowScaledTargetAtTwo {radicand} positive =
  subst
    (four ≤_)
    (scaledAtTwoNormalForm radicand)
    (NatP.*-monoʳ-≤ four positive)

candidateTwoInsideCanonicalBound :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  two ≤ suc (FloorApprox.scaledSquareTarget radicand two)
candidateTwoInsideCanonicalBound positive =
  NatP.≤-trans
    (s≤s (s≤s z≤n))
    (NatP.≤-step (fourBelowScaledTargetAtTwo positive))

floorNumeratorAtTwoAtLeastTwo :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  two ≤ FloorApprox.floorSquareRootNumerator radicand two
floorNumeratorAtTwoAtLeastTwo {radicand} positive =
  Floor.floorSquareRootUpToMaximal
    (candidateTwoInsideCanonicalBound positive)
    (fourBelowScaledTargetAtTwo positive)

crossForOneBelowApproximation :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  suc zero * two
  ≤ FloorApprox.floorSquareRootNumerator radicand two * suc zero
crossForOneBelowApproximation {radicand} positive =
  let
    numerator = FloorApprox.floorSquareRootNumerator radicand two
    raw : two ≤ numerator
    raw = floorNumeratorAtTwoAtLeastTwo positive
  in
  subst
    (two ≤_)
    (NatP.*-identityʳ numerator)
    raw

oneBelowApproximationAtTwo :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  (+ 1 / 1) ℚ.≤
    (+ FloorApprox.floorSquareRootNumerator radicand two / two)
oneBelowApproximationAtTwo positive =
  Fraction.natFractionLe
    (crossForOneBelowApproximation positive)

halfBelowOne : (+ 1 / two) ℚ.< (+ 1 / 1)
halfBelowOne =
  ℚ.*<* (ℤ.+<+ (s≤s z≤n))

canonicalFloorSquareRootPositive :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  BishopReal.Positive (Root.canonicalFloorSquareRootReal radicand)
canonicalFloorSquareRootPositive {radicand} positive =
  BishopReal.pos*
    (suc zero ,
      ℚP.<-≤-trans
        halfBelowOne
        (oneBelowApproximationAtTwo positive))

canonicalFloorSquareRootStrictlyPositive :
  ∀ {radicand : Nat} →
  suc zero ≤ radicand →
  BishopReal._<_ BishopReal.0ℝ
    (Root.canonicalFloorSquareRootReal radicand)
canonicalFloorSquareRootStrictlyPositive positive =
  BishopP.posx⇒0<x (canonicalFloorSquareRootPositive positive)

bishopNatSquareRootPositiveLevel : ProofLevel
bishopNatSquareRootPositiveLevel = machineChecked
