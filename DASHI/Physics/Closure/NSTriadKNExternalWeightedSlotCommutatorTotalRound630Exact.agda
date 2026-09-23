{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorTotalRound630Exact where

------------------------------------------------------------------------
-- ROUND630 / TOTAL EXTERNAL WEIGHTED SLOT COMMUTATOR INCLUDING p = 0
--
-- R629 proves the nonzero-p identity
--
--   weightedExternalSlot(tau)
--     = weight(tau) * doubleExternalCommutator(tau).
--
-- R613 already defines the ACTUAL exhaustive external companion by cases:
--
--   p = 0     -> 0
--   p != 0    -> weightedExternalSlot(tau).
--
-- Therefore the total literal carrier is obtained by the same executable
-- mode-equality split, using R621.modeDifferentFromFalse to construct the
-- required NonZeroMode witness in the false branch.
--
-- The doubled R573 external nested cell then inherits the total commutator
-- representation exactly.  No norm, absolute value, sign estimate, shell
-- decomposition, spacetime integration, or PDE estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedSelectionRound621Exact as R621
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorRound629Exact as R629

module TotalExternalCommutator630
    {r} {F : C3.RealField r}
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

  module Comm =
    R629.ExternalSlotCommutator629 W S L H system velocityTransverse

  pNonzeroFromFalse :
    (tau : Physical.PhysicalTriadIncidence) →
    Output.modeEqual (Physical.p tau) Z3.zeroMode ≡ false →
    Z3.NonZeroMode (Physical.p tau)
  pNonzeroFromFalse tau decision =
    record
      { Z3.notZero =
          R621.modeDifferentFromFalse decision
      }

  totalExternalExhaustiveCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  totalExternalExhaustiveCommutator tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero F
  ... | false =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Add
        (Comm.Ext.externalCommutatorCell tau)
        (Comm.Ext.externalCommutatorCell tau))

  externalExhaustiveCompanionIsTotalCommutator :
    (tau : Physical.PhysicalTriadIncidence) →
    Split.externalExhaustiveCompanion tau
    ≡ totalExternalExhaustiveCommutator tau
  externalExhaustiveCompanionIsTotalCommutator tau
      with Output.modeEqual (Physical.p tau) Z3.zeroMode in decision
  ... | true = refl
  ... | false =
    Comm.weightedExternalSlotIsWeightedDoubleExternalCell
      tau
      (pNonzeroFromFalse tau decision)

  totalExternalNestedCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  totalExternalNestedCommutator tau =
    C3.complex3Add
      (totalExternalExhaustiveCommutator tau)
      (totalExternalExhaustiveCommutator tau)

  externalNestedWeightedCompanionIsTotalCommutator :
    (tau : Physical.PhysicalTriadIncidence) →
    Split.externalNestedWeightedCompanionCell tau
    ≡ totalExternalNestedCommutator tau
  externalNestedWeightedCompanionIsTotalCommutator tau =
    cong₂ C3.complex3Add
      (externalExhaustiveCompanionIsTotalCommutator tau)
      (externalExhaustiveCompanionIsTotalCommutator tau)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round630ExternalExhaustiveCommutatorTotal : Bool
round630ExternalExhaustiveCommutatorTotal = true

round630ZeroPBranchClosed : Bool
round630ZeroPBranchClosed = true

round630R573ExternalNestedCommutatorTotal : Bool
round630R573ExternalNestedCommutatorTotal = true

round630RequiresPNonzeroAssumptionFromCaller : Bool
round630RequiresPNonzeroAssumptionFromCaller = false

round630IntroducesEstimate : Bool
round630IntroducesEstimate = false

round630ExternalSignedPaymentClosed : Bool
round630ExternalSignedPaymentClosed = false

round630ExternalExhaustiveCommutatorTotalIsTrue :
  round630ExternalExhaustiveCommutatorTotal ≡ true
round630ExternalExhaustiveCommutatorTotalIsTrue = refl

round630ZeroPBranchClosedIsTrue :
  round630ZeroPBranchClosed ≡ true
round630ZeroPBranchClosedIsTrue = refl

round630R573ExternalNestedCommutatorTotalIsTrue :
  round630R573ExternalNestedCommutatorTotal ≡ true
round630R573ExternalNestedCommutatorTotalIsTrue = refl

round630RequiresPNonzeroAssumptionFromCallerIsFalse :
  round630RequiresPNonzeroAssumptionFromCaller ≡ false
round630RequiresPNonzeroAssumptionFromCallerIsFalse = refl

round630IntroducesEstimateIsFalse :
  round630IntroducesEstimate ≡ false
round630IntroducesEstimateIsFalse = refl

round630ExternalSignedPaymentClosedIsFalse :
  round630ExternalSignedPaymentClosed ≡ false
round630ExternalSignedPaymentClosedIsFalse = refl
