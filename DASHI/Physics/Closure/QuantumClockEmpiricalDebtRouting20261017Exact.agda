module DASHI.Physics.Closure.QuantumClockEmpiricalDebtRouting20261017Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Physics.Closure.BothwellYe2022AuthorCorrespondenceReceiptExact as Correspondence
import DASHI.Physics.Closure.ZhengKolkowitz2023TransportAttemptReceiptExact as Transport

------------------------------------------------------------------------
-- CLAIM-RELATIVE ROUTING OF THE LIVE CLOCK FRONTIER
--
-- Reuses the canonical repository ProofDebtRouterExact rather than defining a
-- clock-specific debt taxonomy. The central result is operational: the open
-- Bothwell/Ye and Zheng leaves are source-aligned empirical-evidence work, not
-- missing mathematics that should trigger another theorem-generation pass.
--
-- This routing is DASHI workflow logic. It is not attributed to Bothwell/Ye,
-- Zheng/Kolkowitz, Zenodo, BIPM, or any external scientific source.
------------------------------------------------------------------------

record ClockEmpiricalDebtItem : Set where
  field
    itemLabel : String
    routing : Debt.ProofDebtRoutingReceipt
    routedAsEmpiricalEvidenceDebt :
      Debt.routedDebt routing ≡ Debt.empiricalEvidenceDebt
    scheduledAction : Debt.SchedulerAction
    scheduledForEvidenceVerification :
      scheduledAction ≡ Debt.verifyEmpiricalEvidence

open ClockEmpiricalDebtItem public

mkEmpiricalDebtItem : String → ClockEmpiricalDebtItem
mkEmpiricalDebtItem label = record
  { itemLabel = label
  ; routing = Debt.proof-debt-routing-receipt
      Debt.empiricalPremise
      Debt.experimentallySupportedPremise
      Debt.sourceAligned
      Debt.uncertified
      Debt.sourceOnly
      Debt.empiricalEvidenceDebt
      refl
  ; routedAsEmpiricalEvidenceDebt = refl
  ; scheduledAction =
      Debt.scheduleAction
        Debt.empiricalEvidenceDebt
        Debt.sourceAligned
        Debt.standardWorkstation
        Debt.moderateReplay
  ; scheduledForEvidenceVerification = refl
  }

bothwellAuthorEvidenceDebt : ClockEmpiricalDebtItem
bothwellAuthorEvidenceDebt =
  mkEmpiricalDebtItem
    "Bothwell/Ye author-supplied raw arrays and analysis replay"

zhengPublicReplayDebt : ClockEmpiricalDebtItem
zhengPublicReplayDebt =
  mkEmpiricalDebtItem
    "Zheng/Kolkowitz public process-data byte materialisation and replay"

canonicalClockEmpiricalDebtItems : List ClockEmpiricalDebtItem
canonicalClockEmpiricalDebtItems =
  bothwellAuthorEvidenceDebt ∷ zhengPublicReplayDebt ∷ []

record QuantumClockEmpiricalDebtBoundary : Set where
  field
    correspondence : Correspondence.AuthorRequestSendReceipt
    correspondenceIsCanonical :
      correspondence ≡ Correspondence.canonicalBothwellYe2022AuthorRequestSendReceipt

    transportAttempt : Transport.ZhengTransportAttemptReceipt
    transportAttemptIsCanonical :
      transportAttempt ≡ Transport.canonicalZhengTransportAttemptReceipt

    items : List ClockEmpiricalDebtItem

    bothwellEvidenceIsNotMathematicalDebt : Bool
    bothwellEvidenceIsNotMathematicalDebtIsTrue :
      bothwellEvidenceIsNotMathematicalDebt ≡ true

    zhengReplayIsNotMathematicalDebt : Bool
    zhengReplayIsNotMathematicalDebtIsTrue :
      zhengReplayIsNotMathematicalDebt ≡ true

    kernelCertificationIsSeparateDebt : Bool
    kernelCertificationIsSeparateDebtIsTrue :
      kernelCertificationIsSeparateDebt ≡ true

    authorReplyStillRequired : Bool
    authorReplyStillRequiredIsTrue : authorReplyStillRequired ≡ true

    zhengPayloadBytesStillRequired : Bool
    zhengPayloadBytesStillRequiredIsTrue : zhengPayloadBytesStillRequired ≡ true

    reading : List String

open QuantumClockEmpiricalDebtBoundary public

canonicalQuantumClockEmpiricalDebtBoundary : QuantumClockEmpiricalDebtBoundary
canonicalQuantumClockEmpiricalDebtBoundary = record
  { correspondence = Correspondence.canonicalBothwellYe2022AuthorRequestSendReceipt
  ; correspondenceIsCanonical = refl
  ; transportAttempt = Transport.canonicalZhengTransportAttemptReceipt
  ; transportAttemptIsCanonical = refl
  ; items = canonicalClockEmpiricalDebtItems
  ; bothwellEvidenceIsNotMathematicalDebt = true
  ; bothwellEvidenceIsNotMathematicalDebtIsTrue = refl
  ; zhengReplayIsNotMathematicalDebt = true
  ; zhengReplayIsNotMathematicalDebtIsTrue = refl
  ; kernelCertificationIsSeparateDebt = true
  ; kernelCertificationIsSeparateDebtIsTrue = refl
  ; authorReplyStillRequired = true
  ; authorReplyStillRequiredIsTrue = refl
  ; zhengPayloadBytesStillRequired = true
  ; zhengPayloadBytesStillRequiredIsTrue = refl
  ; reading =
      "The canonical ProofDebtRouterExact classifies these source-aligned empirical premises as empiricalEvidenceDebt and schedules evidence verification."
      ∷ "Neither missing author data nor an unavailable public payload transport is evidence of missing mathematics."
      ∷ "Agda kernel certification of DASHI's local formal source is a separate certification coordinate and cannot substitute for the missing experimental bytes."
      ∷ "Conversely, later empirical byte acquisition cannot certify unrelated formal theorem source merely by arriving."
      ∷ []
  }

canonicalBothwellDebtIsEmpirical :
  Debt.routedDebt (routing bothwellAuthorEvidenceDebt) ≡ Debt.empiricalEvidenceDebt
canonicalBothwellDebtIsEmpirical = refl

canonicalZhengDebtIsEmpirical :
  Debt.routedDebt (routing zhengPublicReplayDebt) ≡ Debt.empiricalEvidenceDebt
canonicalZhengDebtIsEmpirical = refl
