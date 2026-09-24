{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarLiveM2PaymentRound663Exact where

------------------------------------------------------------------------
-- ROUND663 / LIVE R661 PAIR-DIFFERENCE -> R662 M2 PAYMENT
--
-- R662 proves on a static literal physical output fibre
--
--   2 PairDiffWork <= nu * M2Budget.
--
-- R661's live bad-collar spacetime normal form uses the SAME full
-- physicalOutputFiber at each (N,t), with modal rate
--
--   rho_t(k) = nu_t |k|^2.
--
-- R240/R408 fix viscosity along the trajectory, and R561 proves the live
-- physical decay rate is exactly the fixed trajectory rate
--
--   rho_t(k) = nu |k|^2.
--
-- Therefore R662 attaches pointwise to the actual R661 scalar:
--
--   2 PairDiffWork_N,k(t) <= nu * M2_N,k(t).
--
-- Adding the untouched positive self-rate coordinate gives
--
--   2 [ SelfRate + PairDiff ]
--     <= 2 SelfRate + nu M2.
--
-- Given only the ordinary monotonicity theorem for integrateTo, this lifts
-- directly to spacetime.  No division by fibre cardinality, comparable-only
-- P3 carrier, or new Navier--Stokes estimate is introduced.
--
-- The remaining local analytic target is now explicitly the spacetime
-- self-rate + M2 budget and its cutoff-uniform output aggregation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredCovarianceFactorExact as Centered
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as Bony
import DASHI.Physics.Closure.NSTriadKNSelfPairFixedResolventTrajectoryRound561Exact as R561
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as Order
import DASHI.Physics.Closure.NSTriadKNR650BadCollarSpacetimePairDifferenceRound661Exact as R661
import DASHI.Physics.Closure.NSTriadKNR650BadCollarPairDifferenceM2PaymentRound662Exact as R662

F : C3.RealField _
F = Rational.rationalRealField

module LiveM2
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R661.R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R661.R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      R661.R594.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R661.R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus :
      R661.R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R661.R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (D :
      R661.R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        (R661.R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Sp = R661.BadCollarSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  module Fixed = R561.FixedSelfPair
    Time initialTime integrateTo VectorDerivativeOf

  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo VectorDerivativeOf

  nu : ℚ
  nu = Fixed.commonNu D

  nuPositive : Positive nu
  nuPositive = Support.physicalViscosityPositive R

  nuNonnegative : 0ℚ ≤ nu
  nuNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ nu)

  modalRateAtFixed :
    (cutoff : Nat) (time : Time) (mode : Z3.FourierMode) →
    Sp.End.rateAt cutoff time mode
    ≡ Centered.modalViscousRate nu Sp.End.I mode
  modalRateAtFixed cutoff time mode =
    trans
      (Fixed.physicalDecayRateFixed561 D cutoff time mode)
      refl

  cellRateAtFixed :
    (cutoff : Nat) (time : Time)
    (tau : Physical.PhysicalTriadIncidence) →
    Pair.cellRate (Sp.End.rateAt cutoff time) tau
    ≡
    Pair.cellRate (Centered.modalViscousRate nu Sp.End.I) tau
  cellRateAtFixed cutoff time tau =
    cong₂ _+_
      (modalRateAtFixed cutoff time (Physical.p tau))
      (modalRateAtFixed cutoff time (Physical.q tau))

  module PayAt
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time) =
    R662.PairDifferenceM2
      {E = Sp.End.E} {I = Sp.End.I}
      nu nuNonnegative Sp.End.S
      (Sp.End.velocityAt cutoff time)
      cutoff output

  pairDifferenceSameObject :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    Sp.pairDifferenceWorkAt cutoff output time
    ≡ PayAt.pairDifference cutoff output time
  pairDifferenceSameObject cutoff output time =
    trans
      (Bony.pairDifferenceRateTransport
        (Pair.cellRate (Sp.End.rateAt cutoff time))
        (Pair.cellRate (Centered.modalViscousRate nu Sp.End.I))
        (Sp.End.workAt cutoff output time)
        (cellRateAtFixed cutoff time)
        (Output.physicalOutputFiber cutoff output))
      refl

  m2BudgetAt :
    Nat → Z3.FourierMode → Time → ℚ
  m2BudgetAt cutoff output time =
    PayAt.P.totalM2Budget cutoff output time
      (PayAt.items cutoff output time)

  livePairDifferenceBelowM2 :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    Pair.two * Sp.pairDifferenceWorkAt cutoff output time
    ≤ nu * m2BudgetAt cutoff output time
  livePairDifferenceBelowM2 cutoff output time =
    subst
      (λ left →
        Pair.two * left
        ≤ nu * m2BudgetAt cutoff output time)
      (sym (pairDifferenceSameObject cutoff output time))
      (PayAt.signedPairDifferenceBelowPhysicalM2 cutoff output time)

  doubledResidualAt :
    Nat → Z3.FourierMode → Time → ℚ
  doubledResidualAt cutoff output time =
    Pair.two *
      ( Sp.rateSelfWorkAt cutoff output time
      + Sp.pairDifferenceWorkAt cutoff output time )

  selfRatePlusM2At :
    Nat → Z3.FourierMode → Time → ℚ
  selfRatePlusM2At cutoff output time =
    Pair.two * Sp.rateSelfWorkAt cutoff output time
      + nu * m2BudgetAt cutoff output time

  liveResidualBelowSelfRatePlusM2 :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    doubledResidualAt cutoff output time
    ≤ selfRatePlusM2At cutoff output time
  liveResidualBelowSelfRatePlusM2 cutoff output time =
    let
      expanded :
        doubledResidualAt cutoff output time
        ≡
        Pair.two * Sp.rateSelfWorkAt cutoff output time
          + Pair.two * Sp.pairDifferenceWorkAt cutoff output time
      expanded =
        solve
          ( Sp.rateSelfWorkAt cutoff output time
          ∷ Sp.pairDifferenceWorkAt cutoff output time
          ∷ [])

      bounded :
        Pair.two * Sp.rateSelfWorkAt cutoff output time
          + Pair.two * Sp.pairDifferenceWorkAt cutoff output time
        ≤ selfRatePlusM2At cutoff output time
      bounded =
        ℚP.+-mono-≤
          ℚP.≤-refl
          (livePairDifferenceBelowM2 cutoff output time)
    in
    subst
      (_≤ selfRatePlusM2At cutoff output time)
      (sym expanded)
      bounded

  integratedDoubledResidual :
    Nat → Z3.FourierMode → Time → ℚ
  integratedDoubledResidual cutoff output terminal =
    integrateTo (doubledResidualAt cutoff output) terminal

  integratedSelfRatePlusM2 :
    Nat → Z3.FourierMode → Time → ℚ
  integratedSelfRatePlusM2 cutoff output terminal =
    integrateTo (selfRatePlusM2At cutoff output) terminal

  liveSpacetimeResidualBelowSelfRatePlusM2 :
    (orderIntegration : Order.IntegrationOrderAuthority Time integrateTo) →
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedDoubledResidual cutoff output terminal
    ≤ integratedSelfRatePlusM2 cutoff output terminal
  liveSpacetimeResidualBelowSelfRatePlusM2
      orderIntegration cutoff output terminal =
    Order.integrateMonotone orderIntegration
      (doubledResidualAt cutoff output)
      (selfRatePlusM2At cutoff output)
      (liveResidualBelowSelfRatePlusM2 cutoff output)
      terminal

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round663LiveRateSameObjectWeldClosed : Bool
round663LiveRateSameObjectWeldClosed = true

round663LivePairDifferenceM2PaymentClosed : Bool
round663LivePairDifferenceM2PaymentClosed = true

round663LiveResidualReducedToSelfRatePlusM2 : Bool
round663LiveResidualReducedToSelfRatePlusM2 = true

round663SpacetimeReductionClosedGivenIntegrationOrder : Bool
round663SpacetimeReductionClosedGivenIntegrationOrder = true

round663SelfRatePlusM2CutoffUniformPaymentClosed : Bool
round663SelfRatePlusM2CutoffUniformPaymentClosed = false

round663SelfRateTermEliminated : Bool
round663SelfRateTermEliminated = false

round663IntroducesNewClayLeaf : Bool
round663IntroducesNewClayLeaf = false

round663C2Closed : Bool
round663C2Closed = false

round663ClayPromotion : Bool
round663ClayPromotion = false

round663LiveRateSameObjectWeldClosedIsTrue :
  round663LiveRateSameObjectWeldClosed ≡ true
round663LiveRateSameObjectWeldClosedIsTrue = refl

round663LivePairDifferenceM2PaymentClosedIsTrue :
  round663LivePairDifferenceM2PaymentClosed ≡ true
round663LivePairDifferenceM2PaymentClosedIsTrue = refl

round663LiveResidualReducedToSelfRatePlusM2IsTrue :
  round663LiveResidualReducedToSelfRatePlusM2 ≡ true
round663LiveResidualReducedToSelfRatePlusM2IsTrue = refl

round663SpacetimeReductionClosedGivenIntegrationOrderIsTrue :
  round663SpacetimeReductionClosedGivenIntegrationOrder ≡ true
round663SpacetimeReductionClosedGivenIntegrationOrderIsTrue = refl

round663SelfRatePlusM2CutoffUniformPaymentClosedIsFalse :
  round663SelfRatePlusM2CutoffUniformPaymentClosed ≡ false
round663SelfRatePlusM2CutoffUniformPaymentClosedIsFalse = refl

round663SelfRateTermEliminatedIsFalse :
  round663SelfRateTermEliminated ≡ false
round663SelfRateTermEliminatedIsFalse = refl

round663IntroducesNewClayLeafIsFalse :
  round663IntroducesNewClayLeaf ≡ false
round663IntroducesNewClayLeafIsFalse = refl

round663C2ClosedIsFalse :
  round663C2Closed ≡ false
round663C2ClosedIsFalse = refl

round663ClayPromotionIsFalse :
  round663ClayPromotion ≡ false
round663ClayPromotionIsFalse = refl
