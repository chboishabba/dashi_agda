module DASHI.Cognition.EpsteinCOUQYLKAssetTransfer20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinBearStructuredFundRecoveryRound20261015Exact as Recovery
import DASHI.Cognition.EpsteinWexnerCOUQFungibleCapitalLifecycle20261015Exact as Capital

------------------------------------------------------------------------
-- C.O.U.Q. -> YLK ASSET-TRANSFER INSTRUMENTS — 2026-10-15
--
-- Instrument-specific values and annual-return aggregate values are separate.
-- The Bear assignment transfers one named investment. The tax return reports a
-- broader unrestricted YLK grant. Neither should be substituted for the other.
------------------------------------------------------------------------

data TransferSurface : Set where
  bearABSInterest : TransferSurface
  secondCityInterest : TransferSurface
  annualReturnAggregateGrant : TransferSurface
  successorFoundationTransfer : TransferSurface

record TransferReceipt : Set where
  constructor transfer-receipt
  field
    label : String
    effectiveDate : String
    source : String
    boundedFinding : String
    surface : TransferSurface
    valueUSD : Nat
    exactInstrument : Bool
    paid : Bool
open TransferReceipt public

bearAssignment2008 : TransferReceipt
bearAssignment2008 = transfer-receipt
  "COUQ irrevocable assignment of Bear ABS Overseas interest to YLK"
  "2008-01-01"
  "Irrevocable Assignment attached to COUQ/YLK foundation records; duplicate transaction lineage reflected in EFTA00597989/EFTA00611329"
  "COUQ, as assignor, irrevocably assigned all right, title and interest in Bear Stearns Asset Backed Securities Overseas Ltd. to YLK Charitable Fund. The instrument records the fund as valuing the interest at USD11,841,632.82 as of 30 June 2007 and notes a later estimated value around USD6,907,849 as of 30 November 2007. Valuation snapshots are not cash consideration or final realised recovery."
  bearABSInterest 11841632 true true

secondCityAssignment2008 : TransferReceipt
secondCityAssignment2008 = transfer-receipt
  "COUQ irrevocable assignment of Second City Capital interest to YLK"
  "2008-01-01"
  "Irrevocable Assignment attached to COUQ 2007/2008 foundation-return materials"
  "A separate assignment transfers all COUQ right, title and interest in Second City Capital Farmers I to YLK as a charitable contribution; the instrument states partner equity of USD6,518,065 as of 30 September 2007. This is a distinct investment from the Bear ABS interest."
  secondCityInterest 6518065 true true

annualYLKGrant2007Return : TransferReceipt
annualYLKGrant2007Return = transfer-receipt
  "COUQ annual-return YLK grant aggregate"
  "fiscal return prepared 2008"
  "COUQ 2007 Federal Statements / Form 990-PF Statement 5"
  "The foundation return reports YLK Charitable Fund as an unrestricted recipient of USD14,267,681 during the year. This annual-return aggregate must not be mechanically equated to the sum of instrument snapshot values because accounting basis, valuation date and included assets can differ."
  annualReturnAggregateGrant 14267681 false true

record TransferBoundary : Set where
  constructor transfer-boundary
  field
    bearAssignmentInstrumentPaid : Bool
    secondCityAssignmentInstrumentPaid : Bool
    annualReturnYLKAggregatePaid : Bool
    bearSnapshotValueEqualsCashGrant : Bool
    instrumentValuesMustSumToReturnAggregate : Bool
    assignmentMeansCOUQOwnsPostTransferRecovery : Bool
    ylkReceiptImpliesWexnerPersonalBeneficialOwnership : Bool
open TransferBoundary public

canonicalTransferBoundary : TransferBoundary
canonicalTransferBoundary = transfer-boundary
  true true true false false false false

data SnapshotValueImpliesCash : Set where
data InstrumentValuesMustEqualAnnualAggregate : Set where
data AssignorOwnsPostAssignmentRecovery : Set where
data CharitableFundImpliesPersonalOwnership : Set where

snapshotDoesNotCreateCash : SnapshotValueImpliesCash → ⊥
snapshotDoesNotCreateCash ()

instrumentValuesDoNotHaveToEqualAnnualAggregate : InstrumentValuesMustEqualAnnualAggregate → ⊥
instrumentValuesDoNotHaveToEqualAnnualAggregate ()

assignorDoesNotOwnPostAssignmentRecovery : AssignorOwnsPostAssignmentRecovery → ⊥
assignorDoesNotOwnPostAssignmentRecovery ()

charitableFundDoesNotCreatePersonalOwnership : CharitableFundImpliesPersonalOwnership → ⊥
charitableFundDoesNotCreatePersonalOwnership ()

------------------------------------------------------------------------
-- Remaining asset-transfer incidence.
------------------------------------------------------------------------

data TransferDebt : Set where
  ylkCompleteAssetReceiptLedger : TransferDebt
  couqClosingBalanceSheet : TransferDebt
  ylkGoverningInstrument : TransferDebt
  postTransferBearDistributions : TransferDebt
  secondCityPostTransferDisposition : TransferDebt
  taxBasisFairValueReconciliation : TransferDebt

record TransferAcquisition : Set where
  constructor transfer-acquisition
  field
    debt : TransferDebt
    priority : Nat
    question : String
open TransferAcquisition public

canonicalTransferAcquisition : List TransferAcquisition
canonicalTransferAcquisition =
  transfer-acquisition ylkCompleteAssetReceiptLedger 100
    "Reconstruct every asset received by YLK from COUQ/other predecessor vehicles and reconcile instrument-level transfers to Form 990/1023 aggregate reporting." ∷
  transfer-acquisition postTransferBearDistributions 100
    "Trace all Bear ABS cash/in-kind wind-down distributions after the January 2008 assignment to YLK, including the >USD3m interim amount asserted by Bear respondents." ∷
  transfer-acquisition couqClosingBalanceSheet 99
    "Reconcile COUQ pre-transfer investment book/fair values, charitable transfers, liabilities and remaining assets without treating one valuation date as another." ∷
  transfer-acquisition ylkGoverningInstrument 99
    "Resolve YLK governance, trustees/directors, charitable restrictions and decision authority separately from asset receipt." ∷
  transfer-acquisition secondCityPostTransferDisposition 98
    "Trace the Second City interest after assignment and identify distributions/exit value attributable to YLK." ∷
  transfer-acquisition taxBasisFairValueReconciliation 98
    "Reconcile tax basis, fair-market value, partner equity and annual-return grant values for the transferred interests."
  ∷ []
