module DASHI.Cognition.EpsteinApolloIPOShareCountDiscrepancy20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- APOLLO IPO SHARE-COUNT SOURCE CONFLICT — 2026-10-14
--
-- Dechert's Apollo Conflicts Committee report states 263,257 shares.
-- Multiple released brokerage/accounting records state 263,157 shares.
-- We preserve both literal sources rather than silently correcting either.
------------------------------------------------------------------------

record ShareCountReceipt : Set where
  constructor share-count-receipt
  field
    label : String
    source : String
    count : Nat
    boundedFinding : String
    sourcePaid : Bool
open ShareCountReceipt public

dechertCount : ShareCountReceipt
dechertCount = share-count-receipt
  "Dechert/Apollo commissioned-review count"
  "SEC-filed Dechert report, 2021-01-22"
  263257
  "Dechert states Financial Trust purchased 263,257 Apollo shares in the 2011 IPO directed-share program."
  true

portfolioCount : ShareCountReceipt
portfolioCount = share-count-receipt
  "Released portfolio-accounting count"
  "EFTA01344325 / Southern Financial portfolio record"
  263157
  "A released account record carries an Apollo Global Management position of 263,157 shares."
  true

brokerTransferCount : ShareCountReceipt
brokerTransferCount = share-count-receipt
  "2019 brokerage-transfer count"
  "EFTA01372088 / EFTA01384309 / EFTA01383481"
  263157
  "Multiple released 2019 brokerage-transfer records carry an outgoing Apollo Global Management position of 263,157 shares."
  true

record ShareCountConflict : Set where
  constructor share-count-conflict
  field
    commissionedReportCount : Nat
    accountingChainCount : Nat
    discrepancyShares : Nat
    primaryAccountingInternallyConsistent : Bool
    conflictResolvedByAuthorityAlone : Bool
    dechartTypoProved : Bool
open ShareCountConflict public

canonicalShareCountConflict : ShareCountConflict
canonicalShareCountConflict = share-count-conflict
  263257 263157 100 true false false

data CommissionedReportOverridesAccounting : Set where
data AccountingConsistencyProvesReportTypo : Set where

commissionedReportDoesNotOverrideAccounting : CommissionedReportOverridesAccounting → ⊥
commissionedReportDoesNotOverrideAccounting ()

accountingConsistencyDoesNotProveTypo : AccountingConsistencyProvesReportTypo → ⊥
accountingConsistencyDoesNotProveTypo ()

record ShareCountAcquisition : Set where
  constructor share-count-acquisition
  field
    priority : Nat
    question : String
open ShareCountAcquisition public

canonicalShareCountAcquisition : ShareCountAcquisition
canonicalShareCountAcquisition = share-count-acquisition 98
  "Acquire the 2011 directed-share purchase confirmation, transfer-agent ledger and original Apollo IPO allocation record to determine whether 263,257 or 263,157 is the legally settled quantity; preserve the 100-share source conflict until then."
