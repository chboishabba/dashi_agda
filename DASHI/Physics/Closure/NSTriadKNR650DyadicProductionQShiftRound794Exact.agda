{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicProductionQShiftRound794Exact where

------------------------------------------------------------------------
-- ROUND794 / EXPAND THE LITERAL R748 TWO-DIFFERENCE CELL THROUGH q AND q^2
--
-- For beta = (p,q -> k), abbreviate
--
--   X = PairPower(beta)
--   Y = PairPower(pEnergyLeg beta)
--   Z = PairPower(qEnergyLeg beta).
--
-- The corrected q-action gives
--
--   q beta   = (k,-p -> q),
--   q^2 beta = (q,-k -> -p),
--
-- while pEnergyLeg(q beta) = swap beta.  Since orderedPairPower is swap
-- invariant and the dyadic critical weight is even under Fourier negation,
-- the q-shifted R748 cells can be written entirely in the original leg labels.
--
-- No estimate or representation-theory identification is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxComplementRound98Exact as R98C
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNR650SelectedSelfFoldRealityRound719Exact as R719
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777
import DASHI.Physics.Closure.NSTriadKNR650EnergyLegConjugationEquivarianceRound785Exact as R785

F : C3.RealField _
F = Rational.rationalRealField

selectedDyadicWeightNegate :
  (mode : Z3.FourierMode) →
  R748.selectedDyadicWeight (Z3.negateMode mode)
  ≡ R748.selectedDyadicWeight mode
selectedDyadicWeightNegate mode
  rewrite R719.modeEqualNegateZero mode
        | R777.literalShellIndexNegate mode =
  refl

orderedPairPowerSwapInvariant :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (beta : Physical.PhysicalTriadIncidence) →
  R38.orderedPairPower E I (Symmetry.swapTriad beta) velocity
  ≡ R38.orderedPairPower E I beta velocity
orderedPairPowerSwapInvariant {E} {I} velocity beta =
  let
    base = R38.orderedPower E I beta velocity
    swapped = R38.orderedPower E I (Symmetry.swapTriad beta) velocity
  in
  trans
    (R38.orderedPairPowerIsOrderedPlusSwap
      E I (Symmetry.swapTriad beta) velocity)
    (trans
      (cong
        (λ selected → swapped + R38.orderedPower E I selected velocity)
        (R38.swapTriadInvolutiveExact beta))
      (trans
        (solve (base ∷ swapped ∷ []))
        (sym
          (R38.orderedPairPowerIsOrderedPlusSwap
            E I beta velocity))))

module QShift
    ∀ {E : C3.IntegerEmbedding F}
      {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (reality : Reality.RealityCondition (Audit.velocity system))
    (divergenceFree : Reality.DivergenceFreeCondition E (Audit.velocity system))
    (beta : Physical.PhysicalTriadIncidence) where

  velocity = Audit.velocity system

  q1 : Physical.PhysicalTriadIncidence
  q1 = Orbit.qEnergyLeg beta

  q2 : Physical.PhysicalTriadIncidence
  q2 = Orbit.qEnergyLeg q1

  wk wp wq : ℚ
  wk = R748.selectedDyadicWeight (Physical.k beta)
  wp = R748.selectedDyadicWeight (Physical.p beta)
  wq = R748.selectedDyadicWeight (Physical.q beta)

  X Y Z Z2 : ℚ
  X = R38.orderedPairPower E I beta velocity
  Y = R38.orderedPairPower E I (Orbit.pEnergyLeg beta) velocity
  Z = R38.orderedPairPower E I q1 velocity
  Z2 = R38.orderedPairPower E I q2 velocity

  baseCellMeaning :
    R748.pairedProductionTwoDifferenceCell system beta
    ≡ (wk - wq) * X + (wp - wq) * Y
  baseCellMeaning = refl

  q1CellMeaning :
    R748.pairedProductionTwoDifferenceCell system q1
    ≡ (wq - wp) * Z + (wk - wp) * X
  q1CellMeaning =
    let
      pAfterQPower :
        R38.orderedPairPower E I (Orbit.pEnergyLeg q1) velocity ≡ X
      pAfterQPower =
        trans
          (cong
            (λ selected → R38.orderedPairPower E I selected velocity)
            (R785.pAfterQIsSwap beta))
          (orderedPairPowerSwapInvariant velocity beta)
    in
    rewrite selectedDyadicWeightNegate (Physical.p beta)
          | pAfterQPower =
      refl

  q2CellMeaning :
    R748.pairedProductionTwoDifferenceCell system q2
    ≡ (wp - wk) * Z2 + (wq - wk) * Z
  q2CellMeaning =
    let
      pAfterQ2Power :
        R38.orderedPairPower E I (Orbit.pEnergyLeg q2) velocity ≡ Z
      pAfterQ2Power =
        trans
          (cong
            (λ selected → R38.orderedPairPower E I selected velocity)
            (R785.pAfterQIsSwap q1))
          (orderedPairPowerSwapInvariant velocity q1)
    in
    rewrite selectedDyadicWeightNegate (Physical.p beta)
          | selectedDyadicWeightNegate (Physical.k beta)
          | pAfterQ2Power =
      refl

  baseThreeLegZero : X + Y + Z ≡ 0
  baseThreeLegZero =
    R98C.threeLegOrderedPowerZero
      E I velocity reality divergenceFree beta

  q1ThreeLegZero : Z + X + Z2 ≡ 0
  q1ThreeLegZero =
    let
      raw =
        R98C.threeLegOrderedPowerZero
          E I velocity reality divergenceFree q1
      pAfterQPower :
        R38.orderedPairPower E I (Orbit.pEnergyLeg q1) velocity ≡ X
      pAfterQPower =
        trans
          (cong
            (λ selected → R38.orderedPairPower E I selected velocity)
            (R785.pAfterQIsSwap beta))
          (orderedPairPowerSwapInvariant velocity beta)
    in
    trans
      (cong (λ selected → Z + selected + Z2) pAfterQPower)
      raw

  YEliminated : Y ≡ - (X + Z)
  YEliminated =
    let shifted = cong (λ value → value - (X + Z)) baseThreeLegZero
    in
    trans
      (solve (X ∷ Y ∷ Z ∷ []))
      (trans shifted (solve (X ∷ Z ∷ [])))

  Z2Eliminated : Z2 ≡ - (Z + X)
  Z2Eliminated =
    let shifted = cong (λ value → value - (Z + X)) q1ThreeLegZero
    in
    trans
      (solve (X ∷ Z ∷ Z2 ∷ []))
      (trans shifted (solve (X ∷ Z ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round794DyadicCriticalWeightNegationInvariant : Bool
round794DyadicCriticalWeightNegationInvariant = true

round794OrderedPairPowerSwapInvariant : Bool
round794OrderedPairPowerSwapInvariant = true

round794Q1TwoDifferenceExpandedInBaseLabels : Bool
round794Q1TwoDifferenceExpandedInBaseLabels = true

round794Q2TwoDifferenceExpandedInBaseLabels : Bool
round794Q2TwoDifferenceExpandedInBaseLabels = true

round794IntroducesEstimate : Bool
round794IntroducesEstimate = false

round794W2Closed : Bool
round794W2Closed = false

round794ClayPromotion : Bool
round794ClayPromotion = false

round794IntroducesEstimateIsFalse :
  round794IntroducesEstimate ≡ false
round794IntroducesEstimateIsFalse = refl

round794W2ClosedIsFalse :
  round794W2Closed ≡ false
round794W2ClosedIsFalse = refl

round794ClayPromotionIsFalse :
  round794ClayPromotion ≡ false
round794ClayPromotionIsFalse = refl
