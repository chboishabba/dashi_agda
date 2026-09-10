module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassEnvelopeBidiExact where

------------------------------------------------------------------------
-- EXACT LIVE SPECTATOR-WEIGHTED CLASS ENVELOPE
--
-- The R582 budget existence layer is compiler-owned: exact self ceilings always
-- inhabit it.  Therefore expose the actual finite object whose useful uniform
-- control is the remaining analytic task.
--
-- Graph-colouring cross-pollination (without importing the separate colouring
-- branch): a palette relabelling may be quotiented only after the downstream
-- consumer is invariant under that relabelling.  Here the physical p/q swap
-- exchanges the Bony labels LH <-> HL.  The slot-transformed owner proves that
-- the ACTUAL R584 LH and HL folds are equal, so the four displayed class labels
-- descend to three independent analytic orbit coordinates:
--
--   {LH,HL}, {HH->low}, {comparable}.
--
-- This is a consumer-relative quotient, not an identification of the raw tags.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _≤_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNFourSignBonyClassGramCompilerRound580Exact as R580
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNClassNormBudgetToBonyGramPaymentRound582Exact as R582
import DASHI.Physics.Closure.NSTriadKNDirectBonyClassNormCompilerRound583Exact as R583
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact as SpectatorBony
import DASHI.Physics.Closure.NSTriadKNExactBonyClassNormSelfBudgetBidiExact as SelfBudget
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyLHHLNormSymmetryBidiExact as SlotSymmetry

F : C3.RealField _
F = Rational.rationalRealField

module ExactEnvelope
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module SB = SpectatorBony.SpectatorWeightedNestedBony
    physicalSystem S L H velocityTransverse

  module AtSpectator (beta : Physical.PhysicalTriadIncidence) where
    module Live = SB.Live beta
    module Sym = SlotSymmetry.SlotSymmetry
      (SB.Spec.spectatorWeight beta) S L H SB.system velocityTransverse

    cells : Physical.PhysicalTriadIncidence → R580.FourBonyClassCells580
    cells tau = Live.nestedSlotCells584 tau

    exactClassBudgets :
      (tau : Physical.PhysicalTriadIncidence) →
      Live.NestedSlotClassNormPayment584 tau
    exactClassBudgets tau =
      Live.nested-slot-class-norm-payment-584
        (SelfBudget.exactFourBonyClassSelfBudgets (cells tau))

    lowHighNorm highLowNorm highHighToLowNorm comparableNorm :
      Physical.PhysicalTriadIncidence → ℚ
    lowHighNorm tau = L2.complex3NormSquared (R580.lowHighSum580 (cells tau))
    highLowNorm tau = L2.complex3NormSquared (R580.highLowSum580 (cells tau))
    highHighToLowNorm tau =
      L2.complex3NormSquared (R580.highHighToLowSum580 (cells tau))
    comparableNorm tau =
      L2.complex3NormSquared (R580.comparableSum580 (cells tau))

    exactFourClassEnvelope : Physical.PhysicalTriadIncidence → ℚ
    exactFourClassEnvelope tau =
      R583.fourClassNormEnvelope583
        (cells tau)
        (Live.budgets584 (exactClassBudgets tau))

    exactFourNormSum : Physical.PhysicalTriadIncidence → ℚ
    exactFourNormSum tau =
      lowHighNorm tau + highLowNorm tau
        + highHighToLowNorm tau + comparableNorm tau

    exactFourClassEnvelopeMeaning :
      (tau : Physical.PhysicalTriadIncidence) →
      exactFourClassEnvelope tau ≡ exactFourNormSum tau
    exactFourClassEnvelopeMeaning tau = refl

    lowHighSumIsFold :
      (tau : Physical.PhysicalTriadIncidence) →
      R580.lowHighSum580 (cells tau)
      ≡ R224.foldVector
          (R581.lowHighCell581 (Live.nestedSlotCell584 tau))
          (Output.physicalOutputFiber
            (Audit.cutoff SB.system) (Physical.p tau))
    lowHighSumIsFold tau =
      R581.sumCellsMapAsFold581
        (R581.lowHighCell581 (Live.nestedSlotCell584 tau))
        (Output.physicalOutputFiber
          (Audit.cutoff SB.system) (Physical.p tau))

    highLowSumIsFold :
      (tau : Physical.PhysicalTriadIncidence) →
      R580.highLowSum580 (cells tau)
      ≡ R224.foldVector
          (R581.highLowCell581 (Live.nestedSlotCell584 tau))
          (Output.physicalOutputFiber
            (Audit.cutoff SB.system) (Physical.p tau))
    highLowSumIsFold tau =
      R581.sumCellsMapAsFold581
        (R581.highLowCell581 (Live.nestedSlotCellCell584 tau))
        (Output.physicalOutputFiber
          (Audit.cutoff SB.system) (Physical.p tau))

    lowHighNormEqualsHighLowNorm :
      (tau : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.p tau) →
      lowHighNorm tau ≡ highLowNorm tau
    lowHighNormEqualsHighLowNorm tau pNonzero =
      cong L2.complex3NormSquared
        (trans
          (lowHighSumIsFold tau)
          (trans
            (Sym.nestedSlotLowHighEqualsHighLow tau pNonzero)
            (sym (highLowSumIsFold tau))))

    exactThreeOrbitEnvelope : Physical.PhysicalTriadIncidence → ℚ
    exactThreeOrbitEnvelope tau =
      lowHighNorm tau + lowHighNorm tau
        + highHighToLowNorm tau + comparableNorm tau

    exactFourDescendsToThreeOrbitEnvelope :
      (tau : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.p tau) →
      exactFourClassEnvelope tau ≡ exactThreeOrbitEnvelope tau
    exactFourDescendsToThreeOrbitEnvelope tau pNonzero =
      trans
        (exactFourClassEnvelopeMeaning tau)
        (cong
          (λ middle →
            lowHighNorm tau + middle
              + highHighToLowNorm tau + comparableNorm tau)
          (sym (lowHighNormEqualsHighLowNorm tau pNonzero)))

    nestedSlotBelowExactFourClassEnvelope :
      (tau : Physical.PhysicalTriadIncidence) →
      L2.complex3NormSquared (Live.Weighted.nestedSlotFold tau)
      ≤ R576.four * exactFourClassEnvelope tau
    nestedSlotBelowExactFourClassEnvelope tau =
      Live.nestedSlotFoldBelowClassNorms584 tau (exactClassBudgets tau)

    nestedSlotBelowExactThreeOrbitEnvelope :
      (tau : Physical.PhysicalTriadIncidence) →
      (pNonzero : Z3.NonZeroMode (Physical.p tau)) →
      L2.complex3NormSquared (Live.Weighted.nestedSlotFold tau)
      ≤ R576.four * exactThreeOrbitEnvelope tau
    nestedSlotBelowExactThreeOrbitEnvelope tau pNonzero
      rewrite sym (exactFourDescendsToThreeOrbitEnvelope tau pNonzero) =
      nestedSlotBelowExactFourClassEnvelope tau

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

exactSpectatorFourClassEnvelopeExposed : Bool
exactSpectatorFourClassEnvelopeExposed = true

lhHlPaletteOrbitQuotientConsumerPaid : Bool
lhHlPaletteOrbitQuotientConsumerPaid = true

independentAnalyticClassCoordinates : ℚ
independentAnalyticClassCoordinates = 3

arbitraryClassBudgetChoiceStillOnCriticalPath : Bool
arbitraryClassBudgetChoiceStillOnCriticalPath = false

cutoffUniformUpperForExactEnvelopeClosed : Bool
cutoffUniformUpperForExactEnvelopeClosed = false

spacetimeUpperForExactEnvelopeClosed : Bool
spacetimeUpperForExactEnvelopeClosed = false

r503ClosedHere : Bool
r503ClosedHere = false

exactSpectatorFourClassEnvelopeExposedIsTrue :
  exactSpectatorFourClassEnvelopeExposed ≡ true
exactSpectatorFourClassEnvelopeExposedIsTrue = refl

lhHlPaletteOrbitQuotientConsumerPaidIsTrue :
  lhHlPaletteOrbitQuotientConsumerPaid ≡ true
lhHlPaletteOrbitQuotientConsumerPaidIsTrue = refl

arbitraryClassBudgetChoiceStillOnCriticalPathIsFalse :
  arbitraryClassBudgetChoiceStillOnCriticalPath ≡ false
arbitraryClassBudgetChoiceStillOnCriticalPathIsFalse = refl

r503ClosedHereIsFalse : r503ClosedHere ≡ false
r503ClosedHereIsFalse = refl
