{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicProductionQCycleCollectionRound795Exact where

------------------------------------------------------------------------
-- ROUND795 / COLLECT THE THREE q-POSITIONS BEFORE ANY ESTIMATE
--
-- R794 expands the literal R748 two-difference production cell at
--
--   beta, q beta, q^2 beta
--
-- into the original (p,q,k) labels.  Using only the exact three-leg energy
-- cancellations, the complete three-position production cycle collapses to
--
--   3 * [ (w_k - w_p) PairPower(beta)
--         + (w_q - w_p) PairPower(q beta) ].
--
-- This is the exact order-three quotient channel seen by the conjugation-
-- invariant observable.  It is an NS-specific theorem on the literal carrier;
-- no identification with another repository C3/dihedral carrier is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650DyadicProductionQShiftRound794Exact as R794
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744

F : C3.RealField _
F = Rational.rationalRealField

module QCycle
    ∀ {E : C3.IntegerEmbedding F}
      {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (reality : Reality.RealityCondition (Audit.velocity system))
    (divergenceFree : Reality.DivergenceFreeCondition E (Audit.velocity system))
    (beta : Physical.PhysicalTriadIncidence) where

  module S = R794.QShift system reality divergenceFree beta

  cycleProduction : ℚ
  cycleProduction =
    R748.pairedProductionTwoDifferenceCell system beta
      + R748.pairedProductionTwoDifferenceCell system S.q1
      + R748.pairedProductionTwoDifferenceCell system S.q2

  quotientInvariantProduction : ℚ
  quotientInvariantProduction =
    (S.wk - S.wp) * S.X
      + (S.wq - S.wp) * S.Z

  cycleProductionIsThreeQuotientInvariant :
    cycleProduction
    ≡ R744.three * quotientInvariantProduction
  cycleProductionIsThreeQuotientInvariant =
    trans
      (cong
        (λ first →
          first
            + R748.pairedProductionTwoDifferenceCell system S.q1
            + R748.pairedProductionTwoDifferenceCell system S.q2)
        S.baseCellMeaning)
      (trans
        (cong
          (λ second →
            ((S.wk - S.wq) * S.X + (S.wp - S.wq) * S.Y)
              + second
              + R748.pairedProductionTwoDifferenceCell system S.q2)
          S.q1CellMeaning)
        (trans
          (cong
            (λ third →
              ((S.wk - S.wq) * S.X + (S.wp - S.wq) * S.Y)
                + ((S.wq - S.wp) * S.Z + (S.wk - S.wp) * S.X)
                + third)
            S.q2CellMeaning)
          (trans
            (cong
              (λ selected →
                ((S.wk - S.wq) * S.X + (S.wp - S.wq) * selected)
                  + ((S.wq - S.wp) * S.Z + (S.wk - S.wp) * S.X)
                  + ((S.wp - S.wk) * S.Z2 + (S.wq - S.wk) * S.Z))
              S.YEliminated)
            (trans
              (cong
                (λ selected →
                  ((S.wk - S.wq) * S.X
                    + (S.wp - S.wq) * (- (S.X + S.Z)))
                    + ((S.wq - S.wp) * S.Z
                      + (S.wk - S.wp) * S.X)
                    + ((S.wp - S.wk) * selected
                      + (S.wq - S.wk) * S.Z))
                S.Z2Eliminated)
              (solve
                ( R744.three
                ∷ S.wk ∷ S.wp ∷ S.wq
                ∷ S.X ∷ S.Z
                ∷ []))))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round795ThreeQPositionsCollectedExactly : Bool
round795ThreeQPositionsCollectedExactly = true

round795CycleIsThreeCopiesOfNSQuotientChannel : Bool
round795CycleIsThreeCopiesOfNSQuotientChannel = true

round795ImportsForeignPhysicalCarrier : Bool
round795ImportsForeignPhysicalCarrier = false

round795ProductionCycleCancelsIdentically : Bool
round795ProductionCycleCancelsIdentically = false

round795IntroducesEstimate : Bool
round795IntroducesEstimate = false

round795W2Closed : Bool
round795W2Closed = false

round795ClayPromotion : Bool
round795ClayPromotion = false

round795ThreeQPositionsCollectedExactlyIsTrue :
  round795ThreeQPositionsCollectedExactly ≡ true
round795ThreeQPositionsCollectedExactlyIsTrue = refl

round795CycleIsThreeCopiesOfNSQuotientChannelIsTrue :
  round795CycleIsThreeCopiesOfNSQuotientChannel ≡ true
round795CycleIsThreeCopiesOfNSQuotientChannelIsTrue = refl

round795ProductionCycleCancelsIdenticallyIsFalse :
  round795ProductionCycleCancelsIdentically ≡ false
round795ProductionCycleCancelsIdenticallyIsFalse = refl

round795IntroducesEstimateIsFalse :
  round795IntroducesEstimate ≡ false
round795IntroducesEstimateIsFalse = refl

round795W2ClosedIsFalse :
  round795W2Closed ≡ false
round795W2ClosedIsFalse = refl

round795ClayPromotionIsFalse :
  round795ClayPromotion ≡ false
round795ClayPromotionIsFalse = refl
