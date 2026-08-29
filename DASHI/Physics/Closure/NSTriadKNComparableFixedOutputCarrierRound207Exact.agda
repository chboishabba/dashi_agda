module DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact where

------------------------------------------------------------------------
-- ROUND207 / CC GRAM DEBT IS A SAME-OUTPUT OBJECT
--
-- Round206 instantiated the compressed partner Gram ledger on a finite list of
-- localized CC partners, but its list type did not itself enforce that every
-- incidence had the same Fourier output.  The physical Fourier L2 norm is an
-- outer sum over outputs; Gram covariance belongs INSIDE one output fibre.
--
-- This module tightens the carrier.  A fixed-output localized comparable
-- partner is a Round205 physical partner together with literal evidence that
-- its triad output is the selected mode.  The Round181 Gram ledger is then
-- instantiated only on lists carrying that common-output proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as R204

F = R187.F

record FixedOutputLocalizedComparablePartner
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) : Set where
  constructor fixed-output-localized-comparable-partner
  field
    partner : R205.LocalizedComparableRawCurlPartner system
    outputAgreement :
      Physical.k
        (R204.incidence (R205.localizedComparable partner))
      ≡ output

open FixedOutputLocalizedComparablePartner public

fixedOutputPairs :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode} →
  List (FixedOutputLocalizedComparablePartner system output) →
  List R181.CellPair
fixedOutputPairs [] = []
fixedOutputPairs (entry ∷ rest) =
  R205.comparablePartnerCell (partner entry) ∷ fixedOutputPairs rest

fixedOutputPartnerCells :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode} →
  List (FixedOutputLocalizedComparablePartner system output) →
  List (C3.Complex3 F)
fixedOutputPartnerCells entries = R181.pairCells (fixedOutputPairs entries)

fixedOutputBetweenPartnerDebt :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode} →
  List (FixedOutputLocalizedComparablePartner system output) → ℚ
fixedOutputBetweenPartnerDebt entries =
  R181.betweenPartnerDebt (fixedOutputPairs entries)

fixedOutputCompressedGramLedger :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : Z3.FourierMode}
    (entries : List (FixedOutputLocalizedComparablePartner system output)) →
  L2.complex3NormSquared (R180.sumCells (fixedOutputPartnerCells entries))
  ≡ R180.cellMassSum (fixedOutputPartnerCells entries)
    + fixedOutputBetweenPartnerDebt entries
fixedOutputCompressedGramLedger entries =
  R181.compressedPartnerGramLedger (fixedOutputPairs entries)

round207ComparableGramScopedToOneOutput : Bool
round207ComparableGramScopedToOneOutput = true

round207BetweenDistinctOutputsNeedsGramPayment : Bool
round207BetweenDistinctOutputsNeedsGramPayment = false

round207SameOutputBetweenPartnerDebtPaid : Bool
round207SameOutputBetweenPartnerDebtPaid = false

round207PhysicalCCResidualBudgetClosed : Bool
round207PhysicalCCResidualBudgetClosed = false

round207PackageAClosed : Bool
round207PackageAClosed = false

round207ClayPromotion : Bool
round207ClayPromotion = false

round207ComparableGramScopedToOneOutputIsTrue :
  round207ComparableGramScopedToOneOutput ≡ true
round207ComparableGramScopedToOneOutputIsTrue = refl

round207BetweenDistinctOutputsNeedsGramPaymentIsFalse :
  round207BetweenDistinctOutputsNeedsGramPayment ≡ false
round207BetweenDistinctOutputsNeedsGramPaymentIsFalse = refl
