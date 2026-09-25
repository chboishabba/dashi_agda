{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650UnitSelfNestedCommutatorNormalFormRound712Exact where

------------------------------------------------------------------------
-- ROUND712 / R708 UNIT-WEIGHT SELF NESTED CELL = EXHAUSTIVE FOUR-COPY
--            SELECTED-SELF COMMUTATOR
--
-- Avoid inventing a p=0 commutator theorem.  R613 itself is zero on p=0, so
-- define the exact exhaustive self-commutator carrier with the SAME branch:
--
--   Self4*(tau) = 0                         if p_tau = 0,
--               = 4 * SelfCommutator(tau)  otherwise.
--
-- On p != 0, R711 identifies one R613 self slot with two copies of the
-- selected-self commutator.  R613's nested self cell contains two copies of
-- that slot.  At R694's unit weight:
--
--   selfNestedCell(tau) = Self4*(tau).
--
-- This puts the complete R708 self orbit on a literal selected-self commutator
-- carrier without assuming anything about the zero branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNR650SelfWeightedSlotCommutatorRound711Exact as R711

module UnitSelfNormalForm
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  system = Field30.finiteSystem physicalSystem

  module Split =
    R613.NestedNetworkSplit
      R694.unitWeight S L H system velocityTransverse

  module SelfSlot =
    R711.SelfSlotCommutator
      R694.unitWeight S L H system velocityTransverse

  selfCommutatorFourCopies :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  selfCommutatorFourCopies tau =
    let C = SelfSlot.Self.selfCommutatorCell tau in
    C3.complex3Add
      (C3.complex3Add C C)
      (C3.complex3Add C C)

  exhaustiveSelfCommutatorFourCopies :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  exhaustiveSelfCommutatorFourCopies tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero R694.F
  ... | false = selfCommutatorFourCopies tau

  pNonzeroFromDecision :
    (tau : Physical.PhysicalTriadIncidence) →
    Output.modeEqual (Physical.p tau) Z3.zeroMode ≡ false →
    Z3.NonZeroMode (Physical.p tau)
  pNonzeroFromDecision tau pDecision = record
    { Z3.notZero = λ pZero →
        Output.falseNotTrue
          (trans
            (sym pDecision)
            (Output.modeEqualComplete pZero))
    }
    where
    open import Relation.Binary.PropositionalEquality using (sym; trans)

  selfNestedCellIsExhaustiveFourSelfCommutators :
    (tau : Physical.PhysicalTriadIncidence) →
    Split.selfNestedWeightedCompanionCell tau
    ≡ exhaustiveSelfCommutatorFourCopies tau
  selfNestedCellIsExhaustiveFourSelfCommutators tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
  ... | true = R613.zeroPlusZero
  ... | false =
    let
      pNonzero = pNonzeroFromDecision tau pDecision
      C = SelfSlot.Self.selfCommutatorCell tau

      oneSlot :
        Split.weightedSelfSlot tau
        ≡ C3.complex3Add C C
      oneSlot =
        trans
          (SelfSlot.weightedSelfSlotIsWeightedDoubleSelfCell tau pNonzero)
          (R106.complex3ScaleOne (C3.complex3Add C C))
    in
    cong₂ C3.complex3Add oneSlot oneSlot

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round712UnitSelfNestedCellIsExhaustiveFourSelfCommutators : Bool
round712UnitSelfNestedCellIsExhaustiveFourSelfCommutators = true

round712ZeroPBranchPreservedWithoutRawCommutatorClaim : Bool
round712ZeroPBranchPreservedWithoutRawCommutatorClaim = true

round712IntroducesEstimate : Bool
round712IntroducesEstimate = false

round712SelfOrbitCancellationClosed : Bool
round712SelfOrbitCancellationClosed = false

round712ClayPromotion : Bool
round712ClayPromotion = false

round712UnitSelfNestedCellIsExhaustiveFourSelfCommutatorsIsTrue :
  round712UnitSelfNestedCellIsExhaustiveFourSelfCommutators ≡ true
round712UnitSelfNestedCellIsExhaustiveFourSelfCommutatorsIsTrue = refl

round712ZeroPBranchPreservedWithoutRawCommutatorClaimIsTrue :
  round712ZeroPBranchPreservedWithoutRawCommutatorClaim ≡ true
round712ZeroPBranchPreservedWithoutRawCommutatorClaimIsTrue = refl

round712IntroducesEstimateIsFalse :
  round712IntroducesEstimate ≡ false
round712IntroducesEstimateIsFalse = refl

round712SelfOrbitCancellationClosedIsFalse :
  round712SelfOrbitCancellationClosed ≡ false
round712SelfOrbitCancellationClosedIsFalse = refl

round712ClayPromotionIsFalse :
  round712ClayPromotion ≡ false
round712ClayPromotionIsFalse = refl
