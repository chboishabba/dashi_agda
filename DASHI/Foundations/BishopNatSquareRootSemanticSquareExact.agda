module DASHI.Foundations.BishopNatSquareRootSemanticSquareExact where

------------------------------------------------------------------------
-- SEMANTIC SQUARE LAW FOR THE CONSTRUCTED NAT ROOT
--
-- The real is the canonical floor-approximation `Real.mkℝ` value.  We prove
-- directly against vendor/bishop's setoid equality.  Bishop multiplication
-- samples x*x at precision
--
--   2 * (K x ⊔ K x) * n = 2 * K x * n.
--
-- The floor interval and the canonical bound at that exact precision give the
-- required |seq(x*x,n)-N| <= 2/n certificate for `Real._≃_`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base using (NonZero; z≤n)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _+_; _-_; _*_; _≤_; _<_; _≃_; ∣_∣;
   NonNegative; nonNegative; *≤*)
import Data.Rational.Unnormalised.Properties as ℚP
import NonReflectiveQ as ℚSolver
import Real as BishopReal
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Foundations.BishopNatSquareRootApproximationExact as Approximation
import DASHI.Foundations.BishopNatSquareRootCanonicalApproximationExact as Canonical
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Regular
import DASHI.Foundations.RationalDirectedDifferenceAbsoluteBoundExact as Absolute
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as Fraction
import DASHI.Mathematics.NumberTheory.FinitePositiveScaledReciprocalExact as Reciprocal
open import DASHI.Physics.YangMills.CompactLieProofLevel

upperSquareExpansion :
  (a delta : ℚᵘ) →
  ((a ℚ.+ delta) ℚ.* (a ℚ.+ delta))
  ℚ.≃
  ((a ℚ.* a) ℚ.+
    (((a ℚ.* delta) ℚ.+ (a ℚ.* delta)) ℚ.+ (delta ℚ.* delta)))
upperSquareExpansion a delta =
  let open ℚSolver in
  solve 2
    (λ a′ d′ →
      (a′ ⊕ d′) ⊗ (a′ ⊕ d′)
      ⊜
      (a′ ⊗ a′) ⊕ (((a′ ⊗ d′) ⊕ (a′ ⊗ d′)) ⊕ (d′ ⊗ d′)))
    ℚP.≃-refl a delta

canonicalApproximationBelowScale :
  (radicand precision scale : Nat) →
  .{{_ : NonZero precision}} →
  BishopReal.K (Regular.canonicalFloorSquareRootReal radicand) ≤ scale →
  Canonical.canonicalApproximation radicand precision
  ℚ.≤ (+ scale / 1)
canonicalApproximationBelowScale radicand precision scale K≤scale =
  let
    x = Regular.canonicalFloorSquareRootReal radicand
    a = Canonical.canonicalApproximation radicand precision
    aNN = Canonical.canonicalApproximationNonnegative radicand precision
    absIsA : ℚ.∣ a ∣ ≡ a
    absIsA = ℚP.0≤p⇒∣p∣≡p aNN
    absBelowK : ℚ.∣ a ∣ ℚ.< (+ BishopReal.K x / 1)
    absBelowK = BishopReal.canonical-strict-upper-bound x precision
    aBelowK : a ℚ.≤ (+ BishopReal.K x / 1)
    aBelowK =
      ℚP.<⇒≤
        (subst
          (λ left → left ℚ.< (+ BishopReal.K x / 1))
          absIsA
          absBelowK)
    KBelowScale :
      (+ BishopReal.K x / 1) ℚ.≤ (+ scale / 1)
    KBelowScale = Fraction.natFractionLe K≤scale
  in
  ℚP.≤-trans aBelowK KBelowScale

upperIntervalSquareBelowTwoOver :
  (radicand scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  BishopReal.K (Regular.canonicalFloorSquareRootReal radicand) ≤ scale →
  let
    t = Reciprocal.productPrecision scale precision
    a = Canonical.canonicalApproximation radicand t
    delta = Reciprocal.productPrecisionReciprocal scale precision
  in
  ((a ℚ.+ delta) ℚ.* (a ℚ.+ delta))
  ℚ.≤
  ((a ℚ.* a) ℚ.+ (+ 2 / precision))
upperIntervalSquareBelowTwoOver radicand scale precision K≤scale =
  let
    t = Reciprocal.productPrecision scale precision
    a = Canonical.canonicalApproximation radicand t
    delta = Reciprocal.productPrecisionReciprocal scale precision
    scaleQ = Reciprocal.scaleRational scale

    instance
      deltaNN : NonNegative delta
      deltaNN = ℚ.nonNegative (ℚ.*≤* (ℤ.+≤+ z≤n))

    a≤scale : a ℚ.≤ scaleQ
    a≤scale = canonicalApproximationBelowScale radicand t scale K≤scale

    aDelta≤scaleDelta :
      (a ℚ.* delta) ℚ.≤ (scaleQ ℚ.* delta)
    aDelta≤scaleDelta =
      ℚP.*-monoˡ-≤-nonNeg delta a≤scale

    doubledProductBound :
      ((a ℚ.* delta) ℚ.+ (a ℚ.* delta))
      ℚ.≤ (+ 1 / precision)
    doubledProductBound =
      ℚP.≤-trans
        (ℚP.+-mono-≤ aDelta≤scaleDelta aDelta≤scaleDelta)
        (ℚP.≤-reflexive
          (Reciprocal.doubleScaledReciprocalEquivalent scale precision))

    deltaSquareBound :
      (delta ℚ.* delta) ℚ.≤ (+ 1 / precision)
    deltaSquareBound =
      Reciprocal.reciprocalSquareBelowOneOverPrecision scale precision

    incrementBound :
      (((a ℚ.* delta) ℚ.+ (a ℚ.* delta)) ℚ.+ (delta ℚ.* delta))
      ℚ.≤ (+ 2 / precision)
    incrementBound =
      ℚP.≤-trans
        (ℚP.+-mono-≤ doubledProductBound deltaSquareBound)
        (ℚP.≤-reflexive
          (Reciprocal.oneOverPlusOneOverEquivalentTwoOver precision))

    expandedBound :
      ((a ℚ.* a) ℚ.+
        (((a ℚ.* delta) ℚ.+ (a ℚ.* delta)) ℚ.+ (delta ℚ.* delta)))
      ℚ.≤
      ((a ℚ.* a) ℚ.+ (+ 2 / precision))
    expandedBound = ℚP.+-monoʳ-≤ (a ℚ.* a) incrementBound
  in
  ℚP.≤-trans
    (ℚP.≤-reflexive (upperSquareExpansion a delta))
    expandedBound

squareErrorAtVendorProductPrecision :
  (radicand scale precision : Nat) →
  .{{_ : NonZero scale}} →
  .{{_ : NonZero precision}} →
  BishopReal.K (Regular.canonicalFloorSquareRootReal radicand) ≤ scale →
  let
    t = Reciprocal.productPrecision scale precision
    a = Canonical.canonicalApproximation radicand t
    N = Approximation.natAsRational radicand
  in
  ℚ.∣ (a ℚ.* a) ℚ.- N ∣ ℚ.≤ (+ 2 / precision)
squareErrorAtVendorProductPrecision radicand scale precision K≤scale =
  let
    t = Reciprocal.productPrecision scale precision
    a = Canonical.canonicalApproximation radicand t
    a² = a ℚ.* a
    N = Approximation.natAsRational radicand
    err = + 2 / precision

    instance
      zeroNN : NonNegative 0ℚᵘ
      zeroNN = ℚ.nonNegative (ℚ.*≤* (ℤ.+≤+ z≤n))

      errNN : NonNegative err
      errNN = ℚ.nonNegative (ℚ.*≤* (ℤ.+≤+ z≤n))

    below : a² ℚ.≤ N
    below = Canonical.canonicalApproximationSquareBelow radicand t

    belowWithZero : a² ℚ.≤ N ℚ.+ 0ℚᵘ
    belowWithZero =
      ℚP.≤-trans below (ℚP.p≤p+q N 0ℚᵘ)

    aboveByUpper :
      N ℚ.≤
      ((a ℚ.+ (+ 1 / t)) ℚ.* (a ℚ.+ (+ 1 / t)))
    aboveByUpper = Canonical.radicandBelowCanonicalUpperSquare radicand t

    upperToError :
      ((a ℚ.+ (+ 1 / t)) ℚ.* (a ℚ.+ (+ 1 / t)))
      ℚ.≤ a² ℚ.+ err
    upperToError =
      upperIntervalSquareBelowTwoOver radicand scale precision K≤scale

    above : N ℚ.≤ a² ℚ.+ err
    above = ℚP.≤-trans aboveByUpper upperToError

    raw = Absolute.absoluteDifferenceBound
      {x = a²} {y = N} {leftError = err} {rightError = 0ℚᵘ}
      belowWithZero above
  in
  ℚP.≤-trans raw
    (ℚP.≤-reflexive (ℚP.+-identityʳ err))

canonicalFloorSquareRootSquaresToNat :
  (radicand : Nat) →
  BishopReal._≃_
    (BishopReal._*_
      (Regular.canonicalFloorSquareRootReal radicand)
      (Regular.canonicalFloorSquareRootReal radicand))
    (BishopReal._⋆ (Approximation.natAsRational radicand))
canonicalFloorSquareRootSquaresToNat radicand =
  let x = Regular.canonicalFloorSquareRootReal radicand in
  rewrite NatP.⊔-idem (BishopReal.K x) in
  BishopReal.*≃* λ {(suc precision-1) →
    squareErrorAtVendorProductPrecision
      radicand
      (BishopReal.K x)
      (suc precision-1)
      NatP.≤-refl}

bishopNatSquareRootSemanticSquareLevel : ProofLevel
bishopNatSquareRootSemanticSquareLevel = machineChecked
