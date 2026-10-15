module DASHI.Cognition.EpsteinWexnerRecoveryScopeReconciliation20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinYLKAssetReturnLifecycle20261015Exact as YLK
import DASHI.Cognition.EpsteinWexnerTrusteeTenureBoundary20261015Exact as Tenure

------------------------------------------------------------------------
-- WEXNER RECOVERY SCOPE RECONCILIATION — 2026-10-15
--
-- An official prosecution memorandum records Wexner counsel's account of a
-- negotiated USD100m return in January 2008. Filed charity returns independently
-- pay USD46.658m flowing into YLK. The public records do not yet establish
-- whether that charitable transfer is inside, outside, or partly overlapping
-- the USD100m settlement/recovery amount. No additive total is therefore made.
------------------------------------------------------------------------

data RecoverySourceClass : Set where
  federalProsecutionMemoRecordingCounselAccount : RecoverySourceClass
  filedCharityReturn : RecoverySourceClass
  foundationCommissionedReview : RecoverySourceClass
  executedSettlementInstrument : RecoverySourceClass

record RecoveryScopeReceipt : Set where
  constructor recovery-scope-receipt
  field
    label : String
    dateOrPeriod : String
    sourceClass : RecoverySourceClass
    source : String
    boundedFinding : String
    amountUSD : Nat
    paymentOrTransferPaid : Bool
    adjudicatedMisappropriationPaid : Bool
open RecoveryScopeReceipt public

hundredMillionCounselAccount : RecoveryScopeReceipt
hundredMillionCounselAccount = recovery-scope-receipt
  "Wexner counsel account of private USD100m recovery"
  "January 2008"
  federalProsecutionMemoRecordingCounselAccount
  "DOJ/FBI prosecution memorandum EFTA02731147 / EFTA_00022526"
  "The released federal memorandum records that the Wexners withdrew Epstein's power of attorney, hired counsel to negotiate a private settlement, and that Epstein agreed to return USD100m, which the memorandum says he did in January 2008. The passage records the Wexner-side account supplied to prosecutors; the public settlement agreement and component ledger are not attached here."
  100000000 true false

ylkInitialTransfer : RecoveryScopeReceipt
ylkInitialTransfer = recovery-scope-receipt
  "COUQ plus FTC transfer into YLK"
  "2008"
  filedCharityReturn
  "YLK 2008 Schedule B"
  "YLK's filed Schedule B records USD12,377,844 from COUQ and USD34,280,154 from Financial Trust, combined USD46,657,998, as noncash contributions."
  46657998 true false

reviewPartialRecovery : RecoveryScopeReceipt
reviewPartialRecovery = recovery-scope-receipt
  "Foundation-review partial-recovery characterization"
  "2020"
  foundationCommissionedReview
  "Wexner Foundation independent review"
  "The foundation-commissioned review accepts the Wexners' account that the YLK transfers represented partial recovery of assets misappropriated from the family. This is an attributed review conclusion, not a judicial finding or public settlement accounting."
  0 false false

record RecoveryScopeBoundary : Set where
  constructor recovery-scope-boundary
  field
    hundredMillionReturnAccountPaid : Bool
    ylkFortySixMillionTransferPaid : Bool
    ylkTransferKnownInsideHundredMillion : Bool
    ylkTransferKnownOutsideHundredMillion : Bool
    hundredMillionPlusYLKMayBeAdded : Bool
    laterYLKDissolutionMayBeAddedAsNewRecovery : Bool
    misappropriationJudiciallyAdjudicatedByTheseReceipts : Bool
    executedPrivateSettlementPubliclyPaid : Bool
open RecoveryScopeBoundary public

canonicalRecoveryScopeBoundary : RecoveryScopeBoundary
canonicalRecoveryScopeBoundary = recovery-scope-boundary
  true true false false false false false false

data HundredMillionPlusYLKIsAdditive : Set where
data YLKDissolutionCreatesNewRecovery : Set where
data CounselAccountCreatesAdjudicatedMisappropriation : Set where

hundredMillionAndYLKCannotBeBlindlyAdded : HundredMillionPlusYLKIsAdditive → ⊥
hundredMillionAndYLKCannotBeBlindlyAdded ()

ylkDissolutionDoesNotCreateSecondRecovery : YLKDissolutionCreatesNewRecovery → ⊥
ylkDissolutionDoesNotCreateSecondRecovery ()

counselAccountDoesNotCreateAdjudication : CounselAccountCreatesAdjudicatedMisappropriation → ⊥
counselAccountDoesNotCreateAdjudication ()

------------------------------------------------------------------------
-- Max-cut: component reconciliation, not amount discovery.
------------------------------------------------------------------------

data RecoveryScopeDebt : Set where
  executedPrivateSettlement : RecoveryScopeDebt
  hundredMillionComponentLedger : RecoveryScopeDebt
  ylkSettlementCrossReference : RecoveryScopeDebt
  propertyAssetReturnSchedule : RecoveryScopeDebt
  powerOfAttorneyRevocationInstrument : RecoveryScopeDebt
  recoveryTaxTreatment : RecoveryScopeDebt

record RecoveryScopeAcquisition : Set where
  constructor recovery-scope-acquisition
  field
    debt : RecoveryScopeDebt
    priority : Nat
    question : String
open RecoveryScopeAcquisition public

canonicalRecoveryScopeAcquisition : List RecoveryScopeAcquisition
canonicalRecoveryScopeAcquisition =
  recovery-scope-acquisition executedPrivateSettlement 100
    "Acquire the executed 2007/08 Wexner-Epstein settlement/recovery agreement and schedules; the prosecution memo pays the counsel account, not the operative contract." ∷
  recovery-scope-acquisition hundredMillionComponentLedger 100
    "Reconcile every cash, security, charity, property, loan and other asset return comprising the reported USD100m without double counting onward transfers." ∷
  recovery-scope-acquisition ylkSettlementCrossReference 100
    "Determine from settlement, correspondence or accounting records whether the USD46.658m YLK capitalization formed part of the USD100m recovery, was additional, or overlapped only in part." ∷
  recovery-scope-acquisition propertyAssetReturnSchedule 99
    "Map any real estate, aircraft, securities or trust-property returns separately from cash/charitable transfers and preserve fair value versus cash consideration." ∷
  recovery-scope-acquisition powerOfAttorneyRevocationInstrument 99
    "Acquire the actual revocation/termination instrument for Epstein's Wexner power of attorney and join its date to the trust/family-office authority unwind." ∷
  recovery-scope-acquisition recoveryTaxTreatment 98
    "Resolve tax/basis treatment of the settlement and charitable asset transfers before classifying their economic incidence."
  ∷ []
