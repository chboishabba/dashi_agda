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

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (_/_; _≤_; _<_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as FloorApprox
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Floor
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fraction
open import DASHI.Physics.YangMills.CompactLieProofLevel

two : Nat
two = suc (suc 0)

four : Nat
four = two * two

fourBelowScaledTargetAtTwo :
  ∀ {radicand : Nat} →
  suc 0 ≤ radicand →
  four ≤ FloorApprox.scaledSquareTarget radicand two
fourBelowScaledTargetAtTwo {radicand} positive =
  let
    fourTimesRadicand : four ≤ radicand * four
    fourTimesRadicand =
      NatP.≤-respʳ-≡
        (NatP.*-comm radicand four)
        (NatP.*-monoʳ-≤ four positive)
  in
  NatP.≤-respʳ-≡
    (let open NatP.≡-Reasoning in
     begin
       radicand * four
         ≡⟨ refl ⟩
       FloorApprox.scaledSquareTarget radicand two
     ∎)
    fourTimesRadicand

candidateTwoInsideCanonicalBound :
  ∀ {radicand : Nat} →
  suc 0 ≤ radicand →
  two ≤ suc (FloorApprox.scaledSquareTarget radicand two)
candidateTwoInsideCanonicalBound positive =
  NatP.≤-trans
    (s≤s (s≤s z≤n))
    (NatP.≤-step (fourBelowScaledTargetAtTwo positive))

floorNumeratorAtTwoAtLeastTwo :
  ∀ {radicand : Nat} →
  suc 0 ≤ radicand →
  two ≤ FloorApprox.floorSquareRootNumerator radicand two
floorNumeratorAtTwoAtLeastTwo {radicand} positive =
  Floor.floorSquareRootUpToMaximal
    (candidateTwoInsideCanonicalBound positive)
    (fourBelowScaledTargetAtTwo positive)

oneBelowApproximationAtTwo :
  ∀ {radicand : Nat} →
  suc 0 ≤ radicand →
  (+ 1 / 1) ℚ.≤
    (+ FloorApprox.floorSquareRootNumerator radicand two / two)
oneBelowApproximationAtTwo positive =
  Fraction.natFractionLe
    (NatP.≤-respʳ-≡
      (NatP.*-identityʳ
        (FloorApprox.floorSquareRootNumerator _ two))
      (floorNumeratorAtTwoAtLeastTwo positive))

halfBelowOne : (+ 1 / two) ℚ.< (+ 1 / 1)
halfBelowOne =
  ℚ.*<* (s≤s (s≤s z≤n))

canonicalFloorSquareRootPositive :
  ∀ {radicand : Nat} →
  suc 0 ≤ radicand →
  BishopReal.Positive (Root.canonicalFloorSquareRootReal radicand)
canonicalFloorSquareRootPositive {radicand} positive =
  BishopReal.pos*
    (suc 0 ,
      ℚP.<-≤-trans
        halfBelowOne
        (oneBelowApproximationAtTwo positive))

canonicalFloorSquareRootStrictlyPositive :
  ∀ {radicand : Nat} →
  suc 0 ≤ radicand →
  BishopReal._<_ BishopReal.0ℝ
    (Root.canonicalFloorSquareRootReal radicand)
canonicalFloorSquareRootStrictlyPositive positive =
  importStrict (canonicalFloorSquareRootPositive positive)
  where
    import RealProperties as BishopP
    importStrict = BishopP.posx⇒0<x

bishopNatSquareRootPositiveLevel : ProofLevel
bishopNatSquareRootPositiveLevel = machineChecked
