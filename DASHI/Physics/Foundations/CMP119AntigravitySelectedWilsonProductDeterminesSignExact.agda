{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedWilsonProductDeterminesSignExact where

------------------------------------------------------------------------
-- WILSON SIGN AND NORMALIZATION: PRODUCT LAW -> COEFFICIENT LAW
--
-- This works on the actual selected CMP119 Section-2 action.  We do not
-- assume c_k = -u_k. Instead the physical Wilson normalization is stated
-- in its source form
--
--          (-c_k) g_k^2 = 1
--
-- for the SAME positive finite-history coupling g_k, whose already-proved
-- CMP109 normalization is u_k g_k^2 = 1.  Rational cancellation proves
-- c_k = -u_k. No separately assumed beta/projector equality is used.
--
-- To close this source leaf, the actual selected Wilson coefficient and
-- its sign-sensitive trace/plaquette normalization must supply the product
-- equality below. The product equality is NOT proved by Eq.(2.23) alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; _*_; _≤_; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

positiveSquare :
  ∀ g → Positive g → Positive (Order.square g)
positiveSquare g positive =
  let
    instance gPos : Positive g
    gPos = positive
    squareGreaterThanZero : 0ℚ < g * g
    squareGreaterThanZero =
      subst
        (_< g * g)
        (ℚP.*-zeroˡ g)
        (ℚP.*-monoˡ-<-pos g (ℚP.positive⁻¹ g))
  in
  ℚ.positive squareGreaterThanZero

cancelPositiveRightProduct :
  ∀ left right factor →
  Positive factor →
  left * factor ≡ right * factor →
  left ≡ right
cancelPositiveRightProduct left right factor positive productEquality =
  let
    instance factorPos : Positive factor
    factorPos = positive
    leftBelowRight : left ≤ right
    leftBelowRight =
      ℚP.*-cancelʳ-≤-pos factor
        (ℚP.≤-reflexive productEquality)
    rightBelowLeft : right ≤ left
    rightBelowLeft =
      ℚP.*-cancelʳ-≤-pos factor
        (ℚP.≤-reflexive (sym productEquality))
  in
  ℚP.≤-antisym leftBelowRight rightBelowLeft

selectedWilsonNegativeInverseFromProduct :
  ∀ c u g →
  Positive g →
  u * Order.square g ≡ 1ℚ →
  (- c) * Order.square g ≡ 1ℚ →
  c ≡ - u
selectedWilsonNegativeInverseFromProduct c u g positive inverseLaw wilsonLaw =
  let
    sameInverse :
      - c ≡ u
    sameInverse =
      cancelPositiveRightProduct
        (- c) u (Order.square g)
        (positiveSquare g positive)
        (trans wilsonLaw (sym inverseLaw))
  in
  trans
    (Ring.solve-∀ c)
    (cong -_ sameInverse)

module _
  {trajectory Mode Atom betaData}
  (history : History.FiniteModeInverseSquareTerminalHistoryData
    trajectory Mode Atom betaData)
  {Density Background Fluctuation Action Wilson E R B Vacuum : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation Action Wilson E R B Vacuum)
  where

  record SelectedWilsonInverseSquareNormalization : Set where
    field
      actualCouplingIsFiniteHistory : ∀ k →
        CMP119.runningCoupling source k ≡ History.couplingAt history k

      actualWilsonProductConvention : ∀ k →
        (- CMP119.wilsonCoefficient source k) *
          Order.square (CMP119.runningCoupling source k)
        ≡ 1ℚ

  open SelectedWilsonInverseSquareNormalization public

  publishedWilsonIsNegativeCMP109Inverse :
    (selected : SelectedWilsonInverseSquareNormalization) →
    ∀ k →
    CMP119.wilsonCoefficient source k
      ≡ - Flow.inverseCoupling trajectory k
  publishedWilsonIsNegativeCMP109Inverse selected k =
    selectedWilsonNegativeInverseFromProduct
      (CMP119.wilsonCoefficient source k)
      (Flow.inverseCoupling trajectory k)
      (History.couplingAt history k)
      (History.couplingPositive history k)
      (History.inverseCouplingRepresentation history k)
      (subst
        (λ actualG →
          (- CMP119.wilsonCoefficient source k) *
            Order.square actualG ≡ 1ℚ)
        (actualCouplingIsFiniteHistory selected k)
        (actualWilsonProductConvention selected k))
