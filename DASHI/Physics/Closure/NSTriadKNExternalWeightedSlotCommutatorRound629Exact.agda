{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorRound629Exact where

------------------------------------------------------------------------
-- ROUND629 / EXTERNAL WEIGHTED SLOT = WEIGHTED DOUBLED COMMUTATOR
--
-- R613 defines, on the nonzero-p branch,
--
--   weightedExternalSlot(tau)
--     = w(tau) * [ i * slotKernel(P,Q,N_p^ext,u_q) ].
--
-- R626 closes the exact transverse-pair hypotheses for N_p^ext and u_q.
-- R307 therefore gives
--
--   i * slotKernel(P,Q,N_p^ext,u_q)
--     = doubleR230Cell(ext)
--     = 2 * externalCommutatorCell(tau).
--
-- Hence the R613 external slot and the R625 external commutator are the SAME
-- physical vector carrier with the factor made explicit.  No estimate,
-- absolute value, shell count or spacetime integration appears here.
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
import DASHI.Physics.Closure.NSTriadKNExternalProductRuleCommutatorRound625Exact as R625
import DASHI.Physics.Closure.NSTriadKNExternalForcingTransverseRound626Exact as R626

F : C3.RealField _
F = Rational.rationalRealField

module ExternalSlotCommutator629
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

  module Ext =
    R625.FixedSystem system S

  externalForcingFunction :
    Physical.PhysicalTriadIncidence →
    Z3.FourierMode →
    C3.Complex3 F
  externalForcingFunction tau mode =
    R95.externalForcingP system tau

  externalDoubleCommutator :
    Physical.PhysicalTriadIncidence →
    C3.Complex3 F
  externalDoubleCommutator tau =
    R306.doubleR230Cell S
      (Audit.velocity system)
      (externalForcingFunction tau)
      tau

  externalDoubleCommutatorIsDoubleExternalCell :
    (tau : Physical.PhysicalTriadIncidence) →
    externalDoubleCommutator tau
    ≡
    C3.complex3Add
      (Ext.externalCommutatorCell tau)
      (Ext.externalCommutatorCell tau)
  externalDoubleCommutatorIsDoubleExternalCell tau = refl

  weightedExternalSlotIsWeightedDoubleCommutator :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    Split.weightedExternalSlot tau
    ≡ C3.complex3Scale (R294.weight W tau)
        (externalDoubleCommutator tau)
  weightedExternalSlotIsWeightedDoubleCommutator tau pNonzero =
    let
      pair =
        R626.externalForcingVelocityPair
          {L = L} {H = H}
          system tau pNonzero
          (velocityTransverse (Physical.q tau))

      slotMeaning =
        R307.doubledForcingCellIsIOuterSlotKernel
          (Audit.velocity system)
          (externalForcingFunction tau)
          tau pair
    in
    cong
      (C3.complex3Scale (R294.weight W tau))
      (Relation.Binary.PropositionalEquality.sym slotMeaning)

  weightedExternalSlotIsWeightedDoubleExternalCell :
    (tau : Physical.PhysicalTriadIncidence) →
    (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
    Split.weightedExternalSlot tau
    ≡
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Add
        (Ext.externalCommutatorCell tau)
        (Ext.externalCommutatorCell tau))
  weightedExternalSlotIsWeightedDoubleExternalCell tau pNonzero =
    trans
      (weightedExternalSlotIsWeightedDoubleCommutator tau pNonzero)
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (externalDoubleCommutatorIsDoubleExternalCell tau))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round629ExternalWeightedSlotCommutatorSameObjectClosed : Bool
round629ExternalWeightedSlotCommutatorSameObjectClosed = true

round629ExternalDoubleCommutatorFactorExplicit : Bool
round629ExternalDoubleCommutatorFactorExplicit = true

round629ExternalTransversalityNoLongerAnalyticDebt : Bool
round629ExternalTransversalityNoLongerAnalyticDebt = true

round629IntroducesEstimate : Bool
round629IntroducesEstimate = false

round629ZeroPBranchHandledHere : Bool
round629ZeroPBranchHandledHere = false

round629ExternalWeightedSlotCommutatorSameObjectClosedIsTrue :
  round629ExternalWeightedSlotCommutatorSameObjectClosed ≡ true
round629ExternalWeightedSlotCommutatorSameObjectClosedIsTrue = refl

round629ExternalDoubleCommutatorFactorExplicitIsTrue :
  round629ExternalDoubleCommutatorFactorExplicit ≡ true
round629ExternalDoubleCommutatorFactorExplicitIsTrue = refl

round629ExternalTransversalityNoLongerAnalyticDebtIsTrue :
  round629ExternalTransversalityNoLongerAnalyticDebt ≡ true
round629ExternalTransversalityNoLongerAnalyticDebtIsTrue = refl

round629IntroducesEstimateIsFalse :
  round629IntroducesEstimate ≡ false
round629IntroducesEstimateIsFalse = refl

round629ZeroPBranchHandledHereIsFalse :
  round629ZeroPBranchHandledHere ≡ false
round629ZeroPBranchHandledHereIsFalse = refl
