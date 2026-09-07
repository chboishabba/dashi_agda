module DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutExact as Two

------------------------------------------------------------------------
-- FINAL ANALYTIC CORES
--
-- The historical payment records intentionally bundled two different kinds of
-- obligation:
--
--   (1) actual analysis: the producer budget fits the consumer allowance;
--   (2) representation: this producer is the same cutoff/taper object consumed
--       by the final pole-quotient assembly.
--
-- For proof search these should not be counted together.  The records below
-- isolate the theorem-bearing analytic cores while preserving the existing
-- payment APIs through exact compilers.
------------------------------------------------------------------------

record OffAnalyticCore : Set₁ where
  constructor off-analytic-core
  field
    target : Off.PoleQuotientOffOrdinateBudgetTarget
    assignedOffAllowance : Off.Scalar target
    offBudgetBelowAssignedAllowance :
      Off._≤_ target
        (Off.OffOrdinateBudget target (Off.universalPoleQuotientTaper target))
        assignedOffAllowance
    analyticReference : String

open OffAnalyticCore public

record OffRepresentationAttachment (core : OffAnalyticCore) : Set₁ where
  constructor off-representation-attachment
  field
    crossingCutoffFeedsThisExactOffProducer : Set
    crossingCutoffFeedsThisExactOffProducerReceipt :
      crossingCutoffFeedsThisExactOffProducer

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    attachmentReference : String

open OffRepresentationAttachment public

compileOffAllowancePayment :
  (core : OffAnalyticCore) ->
  OffRepresentationAttachment core ->
  Payment.PoleQuotientOffAllowancePayment
compileOffAllowancePayment core attachment = record
  { Payment.target = OffAnalyticCore.target core
  ; Payment.assignedOffAllowance = OffAnalyticCore.assignedOffAllowance core
  ; Payment.offBudgetBelowAssignedAllowance =
      OffAnalyticCore.offBudgetBelowAssignedAllowance core
  ; Payment.crossingCutoffFeedsThisExactOffProducer =
      OffRepresentationAttachment.crossingCutoffFeedsThisExactOffProducer attachment
  ; Payment.crossingCutoffFeedsThisExactOffProducerReceipt =
      OffRepresentationAttachment.crossingCutoffFeedsThisExactOffProducerReceipt attachment
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumer =
      OffRepresentationAttachment.sameLiteralPoleQuotientTaperAsFinalConsumer attachment
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      OffRepresentationAttachment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt attachment
  ; Payment.producerReference = OffAnalyticCore.analyticReference core
  }

record GammaAnalyticCore : Set₁ where
  constructor gamma-analytic-core
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    assignedGammaAllowance : Gamma.Scalar target
    gammaBudgetBelowAssignedAllowance :
      Gamma._≤_ target
        (Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target))
        assignedGammaAllowance
    analyticReference : String

open GammaAnalyticCore public

record GammaRepresentationAttachment (core : GammaAnalyticCore) : Set₁ where
  constructor gamma-representation-attachment
  field
    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer
    attachmentReference : String

open GammaRepresentationAttachment public

compileGammaAllowancePayment :
  (core : GammaAnalyticCore) ->
  GammaRepresentationAttachment core ->
  Payment.PoleQuotientGammaAllowancePayment
compileGammaAllowancePayment core attachment = record
  { Payment.target = GammaAnalyticCore.target core
  ; Payment.assignedGammaAllowance = GammaAnalyticCore.assignedGammaAllowance core
  ; Payment.gammaBudgetBelowAssignedAllowance =
      GammaAnalyticCore.gammaBudgetBelowAssignedAllowance core
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumer =
      GammaRepresentationAttachment.sameLiteralPoleQuotientTaperAsFinalConsumer attachment
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      GammaRepresentationAttachment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt attachment
  ; Payment.producerReference = GammaAnalyticCore.analyticReference core
  }

------------------------------------------------------------------------
-- Two analytic cores + representation attachments compile the already-owned
-- terminal two-payment package.  No final consumer is changed.
------------------------------------------------------------------------

record FinalPoleQuotientTwoAnalyticCores : Set₁ where
  constructor final-pole-quotient-two-analytic-cores
  field
    offCore : OffAnalyticCore
    gammaCore : GammaAnalyticCore
    analyticReference : String

open FinalPoleQuotientTwoAnalyticCores public

record FinalPoleQuotientAnalyticCoreAttachments
    (cores : FinalPoleQuotientTwoAnalyticCores) : Set₁ where
  constructor final-pole-quotient-analytic-core-attachments
  field
    offAttachment : OffRepresentationAttachment (offCore cores)
    gammaAttachment : GammaRepresentationAttachment (gammaCore cores)
    attachmentReference : String

open FinalPoleQuotientAnalyticCoreAttachments public

compileFinalTwoPayments :
  (cores : FinalPoleQuotientTwoAnalyticCores) ->
  FinalPoleQuotientAnalyticCoreAttachments cores ->
  Two.FinalPoleQuotientTwoPayments
compileFinalTwoPayments cores attachments =
  Two.final-pole-quotient-two-payments
    (compileOffAllowancePayment
      (offCore cores)
      (offAttachment attachments))
    (compileGammaAllowancePayment
      (gammaCore cores)
      (gammaAttachment attachments))
    (analyticReference cores)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FinalPoleQuotientAnalyticCoreBoundary : Set where
  constructor final-pole-quotient-analytic-core-boundary
  field
    offAnalyticCoreContainsOnlyBudgetFitMathematics : Bool
    offAnalyticCoreContainsOnlyBudgetFitMathematicsIsTrue :
      offAnalyticCoreContainsOnlyBudgetFitMathematics ≡ true

    gammaAnalyticCoreContainsOnlyBudgetFitMathematics : Bool
    gammaAnalyticCoreContainsOnlyBudgetFitMathematicsIsTrue :
      gammaAnalyticCoreContainsOnlyBudgetFitMathematics ≡ true

    cutoffIdentityIsSeparateFromOffAnalysis : Bool
    cutoffIdentityIsSeparateFromOffAnalysisIsTrue :
      cutoffIdentityIsSeparateFromOffAnalysis ≡ true

    taperIdentityIsSeparateFromBothAnalyticCores : Bool
    taperIdentityIsSeparateFromBothAnalyticCoresIsTrue :
      taperIdentityIsSeparateFromBothAnalyticCores ≡ true

    analyticCoresPlusAttachmentsCompileExistingPayments : Bool
    analyticCoresPlusAttachmentsCompileExistingPaymentsIsTrue :
      analyticCoresPlusAttachmentsCompileExistingPayments ≡ true

    offAnalyticCoreInhabitedHere : Bool
    offAnalyticCoreInhabitedHereIsFalse : offAnalyticCoreInhabitedHere ≡ false

    gammaAnalyticCoreInhabitedHere : Bool
    gammaAnalyticCoreInhabitedHereIsFalse : gammaAnalyticCoreInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalPoleQuotientAnalyticCoreBoundary :
  FinalPoleQuotientAnalyticCoreBoundary
canonicalFinalPoleQuotientAnalyticCoreBoundary =
  final-pole-quotient-analytic-core-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The final analytic search target is smaller than the historical payment records suggested. Off analysis is exactly a sharp final Off budget together with its assigned-allowance inequality; crossing-cutoff identity and final-taper identity are representation attachments. Gamma analysis is exactly a sharp final Gamma budget together with its assigned-allowance inequality; final-taper identity is a representation attachment. These cores plus the attachments compile the existing two-payment terminal package. Neither analytic core is fabricated here and RH is not derived."
