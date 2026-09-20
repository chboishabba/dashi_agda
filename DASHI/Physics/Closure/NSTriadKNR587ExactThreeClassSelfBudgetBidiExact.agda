module DASHI.Physics.Closure.NSTriadKNR587ExactThreeClassSelfBudgetBidiExact where

------------------------------------------------------------------------
-- PERIODIC B / EXACT INHABITANTS FOR THE LIVE R587 THREE-CLASS INTERFACE
--
-- R587 reduces the live post-slot inner fibre to three independent class norm
-- coordinates: far-low (LH/HL identified), HH->low, and comparable.
--
-- R582's ClassNormBudget is an interface, not itself an estimate: choosing the
-- exact squared norm of the class sum as the ceiling inhabits it by reflexive
-- order.  NSTriadKNExactBonyClassNormSelfBudgetBidiExact already proves this
-- generically.  This owner instantiates those exact self-budgets on R587's
-- ACTUAL nested-slot class lists.
--
-- Consequence: the remaining B debt is NOT construction of the three dependent
-- budget records.  It is the analytic majorization
--
--   exact class norm <= useful cutoff-uniform / spacetime currency
--
-- for the three live classes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact as R582
import DASHI.Physics.Closure.NSTriadKNExactBonyClassNormSelfBudgetBidiExact as Self
import DASHI.Physics.Closure.NSTriadKNNestedSlotThreeClassNormCompilerRound587Exact as R587
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2

F : C3.RealField _
F = R587.F

module ExactLiveThreeClass
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

  module Live = R587.LiveThreeClass587 W S L H system velocityTransverse

  exactFarLowBudget :
    (outer : Physical.PhysicalTriadIncidence) →
    R582.ClassNormBudget582
      (R580.lowHigh580 (Live.cells587 outer))
  exactFarLowBudget outer =
    Self.exactClassNormSelfBudget
      (R580.lowHigh580 (Live.cells587 outer))

  exactHighHighToLowBudget :
    (outer : Physical.PhysicalTriadIncidence) →
    R582.ClassNormBudget582
      (R580.highHighToLow580 (Live.cells587 outer))
  exactHighHighToLowBudget outer =
    Self.exactClassNormSelfBudget
      (R580.highHighToLow580 (Live.cells587 outer))

  exactComparableBudget :
    (outer : Physical.PhysicalTriadIncidence) →
    R582.ClassNormBudget582
      (R580.comparable580 (Live.cells587 outer))
  exactComparableBudget outer =
    Self.exactClassNormSelfBudget
      (R580.comparable580 (Live.cells587 outer))

  exactThreeClassBudgets :
    (outer : Physical.PhysicalTriadIncidence) →
    Live.ThreeClassNormBudgets587 outer
  exactThreeClassBudgets outer =
    R587.three-class-norm-budgets-587
      (exactFarLowBudget outer)
      (exactHighHighToLowBudget outer)
      (exactComparableBudget outer)

  exactFarLowCeiling :
    Physical.PhysicalTriadIncidence → _
  exactFarLowCeiling outer =
    R582.classNormCeiling582 (exactFarLowBudget outer)

  exactHighHighToLowCeiling :
    Physical.PhysicalTriadIncidence → _
  exactHighHighToLowCeiling outer =
    R582.classNormCeiling582 (exactHighHighToLowBudget outer)

  exactComparableCeiling :
    Physical.PhysicalTriadIncidence → _
  exactComparableCeiling outer =
    R582.classNormCeiling582 (exactComparableBudget outer)

  exactFarLowCeilingMeaning :
    (outer : Physical.PhysicalTriadIncidence) →
    exactFarLowCeiling outer
    ≡ L2.complex3NormSquared
        (DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact.sumCells
          (R580.lowHigh580 (Live.cells587 outer)))
  exactFarLowCeilingMeaning outer = refl

r587ThreeDependentClassBudgetRecordsInhabited : Bool
r587ThreeDependentClassBudgetRecordsInhabited = true

r587ExactSelfBudgetsAreUsefulUniformMajorants : Bool
r587ExactSelfBudgetsAreUsefulUniformMajorants = false

r587RemainingDebtIsUniformMajorizationNotRecordConstruction : Bool
r587RemainingDebtIsUniformMajorizationNotRecordConstruction = true

clayPromotion : Bool
clayPromotion = false

r587ThreeDependentClassBudgetRecordsInhabitedIsTrue :
  r587ThreeDependentClassBudgetRecordsInhabited ≡ true
r587ThreeDependentClassBudgetRecordsInhabitedIsTrue = refl

r587ExactSelfBudgetsAreUsefulUniformMajorantsIsFalse :
  r587ExactSelfBudgetsAreUsefulUniformMajorants ≡ false
r587ExactSelfBudgetsAreUsefulUniformMajorantsIsFalse = refl
