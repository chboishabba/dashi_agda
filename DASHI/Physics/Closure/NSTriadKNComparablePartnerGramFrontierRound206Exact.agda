module DASHI.Physics.Closure.NSTriadKNComparablePartnerGramFrontierRound206Exact where

------------------------------------------------------------------------
-- ROUND206 / EXACT CC PARTNER-GRAM FRONTIER ON THE LOCALIZED PHYSICAL CARRIER
--
-- Round205 supplies the actual localized comparable raw-curl partner object
-- and its universal pointwise partner-mass estimate.  Round181 already proves
-- the exact compressed-partner Gram identity for any finite list of physical
-- partner cells.
--
-- This module instantiates that identity on a finite list of the SAME Round205
-- localized CC objects.  Thus the remaining CC analytic theorem is precisely
-- a quantitative bound on `localizedComparableBetweenPartnerDebt`; there is
-- no remaining abstract-carrier or partner-compression seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205

F = R187.F

localizedComparablePairs :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  List (R205.LocalizedComparableRawCurlPartner system) → List R181.CellPair
localizedComparablePairs [] = []
localizedComparablePairs (partner ∷ rest) =
  R205.comparablePartnerCell partner ∷ localizedComparablePairs rest

localizedComparablePartnerCells :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  List (R205.LocalizedComparableRawCurlPartner system) →
  List (C3.Complex3 F)
localizedComparablePartnerCells partners =
  R181.pairCells (localizedComparablePairs partners)

localizedComparableBetweenPartnerDebt :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  List (R205.LocalizedComparableRawCurlPartner system) → ℚ
localizedComparableBetweenPartnerDebt partners =
  R181.betweenPartnerDebt (localizedComparablePairs partners)

localizedComparableCompressedGramLedger :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (partners : List (R205.LocalizedComparableRawCurlPartner system)) →
  L2.complex3NormSquared
    (R180.sumCells (localizedComparablePartnerCells partners))
  ≡ R180.cellMassSum (localizedComparablePartnerCells partners)
    + localizedComparableBetweenPartnerDebt partners
localizedComparableCompressedGramLedger partners =
  R181.compressedPartnerGramLedger (localizedComparablePairs partners)

-- The intended next producer is quantitative, not a sign theorem:
--
--   localizedComparableBetweenPartnerDebt partners <= R_CC
--
-- for a cutoff-uniform quartic R_CC derived from the Round203 shell collar and
-- the Round205 physical partner masses.
round206LocalizedCCFinitePartnerCarrierConstructed : Bool
round206LocalizedCCFinitePartnerCarrierConstructed = true

round206LocalizedCCExactCompressedGramLedgerClosed : Bool
round206LocalizedCCExactCompressedGramLedgerClosed = true

round206LocalizedCCAbstractCarrierGapRemains : Bool
round206LocalizedCCAbstractCarrierGapRemains = false

round206LocalizedCCBetweenPartnerDebtQuantitativelyPaid : Bool
round206LocalizedCCBetweenPartnerDebtQuantitativelyPaid = false

round206PhysicalCCResidualBudgetClosed : Bool
round206PhysicalCCResidualBudgetClosed = false

round206PackageAClosed : Bool
round206PackageAClosed = false

round206ClayPromotion : Bool
round206ClayPromotion = false

round206LocalizedCCExactCompressedGramLedgerClosedIsTrue :
  round206LocalizedCCExactCompressedGramLedgerClosed ≡ true
round206LocalizedCCExactCompressedGramLedgerClosedIsTrue = refl

round206LocalizedCCAbstractCarrierGapRemainsIsFalse :
  round206LocalizedCCAbstractCarrierGapRemains ≡ false
round206LocalizedCCAbstractCarrierGapRemainsIsFalse = refl

round206LocalizedCCBetweenPartnerDebtQuantitativelyPaidIsFalse :
  round206LocalizedCCBetweenPartnerDebtQuantitativelyPaid ≡ false
round206LocalizedCCBetweenPartnerDebtQuantitativelyPaidIsFalse = refl
