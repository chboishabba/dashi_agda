{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityUnitCouplingCapInverseThresholdExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta

------------------------------------------------------------------------
-- UNIT SMALL-COUPLING CAP -> INVERSE THRESHOLD AT LEAST ONE
--
-- If u_* gamma^2 = 1 with 0 < gamma <= 1, then 1 <= u_*.
-- This is pure rational order algebra.  It does NOT identify any repository
-- coupling cap with the finite-history gamma; that same-object seam remains
-- explicit at the caller.
------------------------------------------------------------------------

squareBelowOneFromUnitCap :
  ∀ {gamma : ℚ} →
  Positive gamma →
  gamma ≤ 1ℚ →
  Order.square gamma ≤ 1ℚ
squareBelowOneFromUnitCap {gamma} gammaPositive gammaBelowOne =
  let
    gammaNN : 0ℚ ≤ gamma
    gammaNN =
      let instance gammaPos : Positive gamma
          gammaPos = gammaPositive
      in ℚP.<⇒≤ (ℚP.positive⁻¹ gamma)

    oneNN : 0ℚ ≤ 1ℚ
    oneNN = ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ)

    squareBelow :
      gamma * gamma ≤ 1ℚ * 1ℚ
    squareBelow =
      ℚP.*-mono-≤
        gammaNN gammaBelowOne
        gammaNN gammaBelowOne
  in
  subst
    (Order.square gamma ≤_)
    (ℚP.*-identityˡ 1ℚ)
    squareBelow

inverseThresholdAtLeastOneFromUnitCap :
  ∀ {gamma inverseThreshold : ℚ} →
  Positive gamma →
  gamma ≤ 1ℚ →
  inverseThreshold * Order.square gamma ≡ 1ℚ →
  1ℚ ≤ inverseThreshold
inverseThresholdAtLeastOneFromUnitCap
    {gamma} {inverseThreshold}
    gammaPositive gammaBelowOne inverseRepresentation =
  let
    gammaSquare = Order.square gamma

    gammaSquarePositive : Positive gammaSquare
    gammaSquarePositive =
      let instance gammaPos : Positive gamma
          gammaPos = gammaPositive
      in ℚP.pos*pos⇒pos gamma gamma

    squareBelowOne :
      gammaSquare ≤ 1ℚ
    squareBelowOne =
      squareBelowOneFromUnitCap gammaPositive gammaBelowOne

    scaled :
      1ℚ * gammaSquare
      ≤
      inverseThreshold * gammaSquare
    scaled =
      subst
        (λ upper → 1ℚ * gammaSquare ≤ upper)
        (sym inverseRepresentation)
        (subst
          (λ right → gammaSquare ≤ right)
          (sym (ℚP.*-identityˡ 1ℚ))
          squareBelowOne)

    instance gammaSquarePos : Positive gammaSquare
    gammaSquarePos = gammaSquarePositive
  in
  ℚP.*-cancelʳ-≤-pos gammaSquare scaled

historyInverseThresholdAtLeastOneFromUnitGamma :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history :
      History.FiniteModeInverseSquareTerminalHistoryData
        trajectory Mode Atom betaData) →
  History.gamma history ≤ 1ℚ →
  1ℚ ≤ History.inverseThreshold history
historyInverseThresholdAtLeastOneFromUnitGamma history gammaBelowOne =
  inverseThresholdAtLeastOneFromUnitCap
    (History.gammaPositive history)
    gammaBelowOne
    (History.inverseThresholdRepresentation history)
