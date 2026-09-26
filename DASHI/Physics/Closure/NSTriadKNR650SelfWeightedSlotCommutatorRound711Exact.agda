{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelfWeightedSlotCommutatorRound711Exact where

------------------------------------------------------------------------
-- ROUND711 / SELECTED-SELF R613 SLOT = WEIGHTED DOUBLED SELF COMMUTATOR
--
-- R613 defines, on p != 0,
--
--   weightedSelfSlot(tau)
--     = w(tau) * [ i K(P,Q,N_p^self,u_q) ].
--
-- R626 supplies transversality of N_p^self and u_q.  The generic R307 forcing
-- slot identity therefore applies exactly.  Using R710's self commutator cell,
--
--   i K(P,Q,N_p^self,u_q)
--     = 2 * SelfCommutatorCell(tau).
--
-- Thus the actual R708 self nested carrier is on the same selected-self
-- commutator vector, with the integer factors explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact as R306
import DASHI.Physics.Closure.NSTriadKNForcingSlotKernelRound307Exact as R307
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNExternalForcingTransverseRound626Exact as R626
import DASHI.Physics.Closure.NSTriadKNR650SelfProductRuleCommutatorRound710Exact as R710

F : C3.RealField _
F = Rational.rationalRealField

module SelfSlotCommutator
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse

  module Self =
    R710.FixedSystem system S

  selfForcingFunction :
    Physical.PhysicalTriadIncidence →
    Z3.FourierMode →
    C3.Complex3 F
  selfForcingFunction tau mode =
    R95.selfForcingP system tau

  selfDoubleCommutator :
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  selfDoubleCommutator tau =
    R306.doubleR230Cell S
      (Audit.velocity system)
      (selfForcingFunction tau)
      tau

  selfDoubleCommutatorIsDoubleSelfCell :
    (tau : Physical.PhysicalTriadIncidence) →
    selfDoubleCommutator tau
    ≡
    C3.complex3Add
      (Self.selfCommutatorCell tau)
      (Self.selfCommutatorCell tau)
  selfDoubleCommutatorIsDoubleSelfCell tau = refl

  selfForcingVelocityPair :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.p tau) →
    R307.TransverseForcingVelocityPair E I S L H
      (Physical.p tau) (Physical.q tau)
      (R95.selfForcingP system tau)
      (Audit.velocity system (Physical.q tau))
  selfForcingVelocityPair tau pNonzero =
    R307.transverse-forcing-velocity-pair
      (R626.selfForcingPTransverse system tau pNonzero)
      (velocityTransverse (Physical.q tau))

  weightedSelfSlotIsWeightedDoubleCommutator :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    Split.weightedSelfSlot tau
    ≡ C3.complex3Scale (R294.weight W tau)
        (selfDoubleCommutator tau)
  weightedSelfSlotIsWeightedDoubleCommutator tau pNonzero =
    let
      pair = selfForcingVelocityPair tau pNonzero

      slotMeaning =
        R307.doubledForcingCellIsIOuterSlotKernel
          (Audit.velocity system)
          (selfForcingFunction tau)
          tau pair
    in
    cong
      (C3.complex3Scale (R294.weight W tau))
      (sym slotMeaning)

  weightedSelfSlotIsWeightedDoubleSelfCell :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    Split.weightedSelfSlot tau
    ≡ C3.complex3Scale (R294.weight W tau)
      (C3.complex3Add
        (Self.selfCommutatorCell tau)
        (Self.selfCommutatorCell tau))
  weightedSelfSlotIsWeightedDoubleSelfCell tau pNonzero =
    trans
      (weightedSelfSlotIsWeightedDoubleCommutator tau pNonzero)
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (selfDoubleCommutatorIsDoubleSelfCell tau))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round711SelfWeightedSlotCommutatorSameObjectClosed : Bool
round711SelfWeightedSlotCommutatorSameObjectClosed = true

round711SelfDoubleCommutatorFactorExplicit : Bool
round711SelfDoubleCommutatorFactorExplicit = true

round711SelfTransversalityNoLongerAnalyticDebt : Bool
round711SelfTransversalityNoLongerAnalyticDebt = true

round711IntroducesEstimate : Bool
round711IntroducesEstimate = false

round711SelfCommutatorAnalyticPaymentClosed : Bool
round711SelfCommutatorAnalyticPaymentClosed = false

round711ClayPromotion : Bool
round711ClayPromotion = false

round711SelfWeightedSlotCommutatorSameObjectClosedIsTrue :
  round711SelfWeightedSlotCommutatorSameObjectClosed ≡ true
round711SelfWeightedSlotCommutatorSameObjectClosedIsTrue = refl

round711SelfDoubleCommutatorFactorExplicitIsTrue :
  round711SelfDoubleCommutatorFactorExplicit ≡ true
round711SelfDoubleCommutatorFactorExplicitIsTrue = refl

round711SelfTransversalityNoLongerAnalyticDebtIsTrue :
  round711SelfTransversalityNoLongerAnalyticDebt ≡ true
round711SelfTransversalityNoLongerAnalyticDebtIsTrue = refl

round711IntroducesEstimateIsFalse :
  round711IntroducesEstimate ≡ false
round711IntroducesEstimateIsFalse = refl

round711ClayPromotionIsFalse :
  round711ClayPromotion ≡ false
round711ClayPromotionIsFalse = refl
