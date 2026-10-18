module DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2GammaCandidateSourceLineageRecoveryExact as Lineage
import DASHI.Analysis.RiemannG2GammaPrecisionLossLocalizationExact as Precision
import DASHI.Analysis.RiemannG2CutoffComplementCoordinateSeparationExact as Coordinate

------------------------------------------------------------------------
-- DIRECT FINAL H_Gamma ALLOWANCE COMPILER
--
-- Unlike H_off, Gamma has no cutoff coordinate in the final consumer.  A final
-- Gamma producer must provide the SAME universal pole-quotient taper, an actual
-- Gamma target/budget theorem, and a downstream-assigned allowance A_Gamma with
--
--   B_Gamma(g_pole) <= A_Gamma.
--
-- The old "fits sharp window : Set" language is deliberately not used as the
-- terminal payment.  The assigned allowance is a literal scalar value and the
-- fit is a theorem in the target's own order.
------------------------------------------------------------------------

record DirectPoleQuotientGammaAllowanceInput : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    assignedGammaAllowance : Gamma.Scalar target

    gammaBudgetBelowAssignedAllowance :
      Gamma._≤_ target
        (Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target))
        assignedGammaAllowance

    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    sameLiteralPoleQuotientTaperAsFinalConsumerReceipt :
      sameLiteralPoleQuotientTaperAsFinalConsumer

    producerReference : String

open DirectPoleQuotientGammaAllowanceInput public

compilePoleQuotientGammaAllowancePayment :
  DirectPoleQuotientGammaAllowanceInput →
  Payment.PoleQuotientGammaAllowancePayment
compilePoleQuotientGammaAllowancePayment input = record
  { Payment.target = target input
  ; Payment.assignedGammaAllowance = assignedGammaAllowance input
  ; Payment.gammaBudgetBelowAssignedAllowance =
      gammaBudgetBelowAssignedAllowance input
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer input
  ; Payment.sameLiteralPoleQuotientTaperAsFinalConsumerReceipt =
      sameLiteralPoleQuotientTaperAsFinalConsumerReceipt input
  ; Payment.producerReference = producerReference input
  }

------------------------------------------------------------------------
-- Repo-first source/search reconciliation.
------------------------------------------------------------------------

data GammaAllowancePayment : Set where
  findAnyGammaBound : GammaAllowancePayment
  recoverAnyGammaSourceFamily : GammaAllowancePayment
  proveRecoveredCandidateIsFinal8889Producer : GammaAllowancePayment
  localizeFirstPrecisionLoss : GammaAllowancePayment
  proveGammaBudgetBelowAssignedAllowance : GammaAllowancePayment
  inventCutoffDependentGammaLaw : GammaAllowancePayment
  compileFinalGammaAllowancePayment : GammaAllowancePayment


data PaymentState : Set where
  owned : PaymentState
  live : PaymentState
  blocked : PaymentState
  downstream : PaymentState
  pruned : PaymentState

paymentState : GammaAllowancePayment → PaymentState
paymentState findAnyGammaBound = pruned
paymentState recoverAnyGammaSourceFamily = pruned
paymentState proveRecoveredCandidateIsFinal8889Producer = owned
paymentState localizeFirstPrecisionLoss = owned
paymentState proveGammaBudgetBelowAssignedAllowance = live
paymentState inventCutoffDependentGammaLaw = pruned
paymentState compileFinalGammaAllowancePayment = downstream

anyGammaBoundSearchPruned :
  paymentState findAnyGammaBound ≡ pruned
anyGammaBoundSearchPruned = refl

anyGammaSourceSearchPruned :
  paymentState recoverAnyGammaSourceFamily ≡ pruned
anyGammaSourceSearchPruned = refl

candidateFinalProducerIdentityOwned :
  paymentState proveRecoveredCandidateIsFinal8889Producer ≡ owned
candidateFinalProducerIdentityOwned = refl

precisionLossLocalizationOwned :
  paymentState localizeFirstPrecisionLoss ≡ owned
precisionLossLocalizationOwned = refl

assignedAllowanceTheoremLive :
  paymentState proveGammaBudgetBelowAssignedAllowance ≡ live
assignedAllowanceTheoremLive = refl

cutoffDependentGammaSearchPruned :
  paymentState inventCutoffDependentGammaLaw ≡ pruned
cutoffDependentGammaSearchPruned = refl

------------------------------------------------------------------------
-- Existing-owner pins.
------------------------------------------------------------------------

candidateGammaFamilyAlreadyRecovered :
  Lineage.GammaCandidateLineageBoundary.concreteGammaSourceFamilyRecovered
    Lineage.canonicalGammaCandidateLineageBoundary ≡ true
candidateGammaFamilyAlreadyRecovered = refl

candidateIdentityWith8889Recovered :
  Lineage.GammaCandidateLineageBoundary.exact8889ConsumerIdentityRecovered
    Lineage.canonicalGammaCandidateLineageBoundary ≡ true
candidateIdentityWith8889Recovered = refl

coarseUniformBoundAlreadyKnown :
  Precision.GammaPrecisionLocalizationBoundary.gammaUpperBoundExistenceIsStillTheResearchQuestion
    Precision.canonicalGammaPrecisionLocalizationBoundary ≡ false
coarseUniformBoundAlreadyKnown = refl

precisionLossLocalizedAtStripConst :
  Precision.GammaPrecisionLocalizationBoundary.exactPrecisionLossStepAlreadyRecoveredOnThisBranch
    Precision.canonicalGammaPrecisionLocalizationBoundary ≡ true
precisionLossLocalizedAtStripConst = refl

gammaHasNoCutoffCoordinate :
  Coordinate.CutoffComplementCoordinateBoundary.existingGammaConsumerHasCutoffArgument
    Coordinate.canonicalCutoffComplementCoordinateBoundary ≡ false
gammaHasNoCutoffCoordinate = refl

record PoleQuotientGammaAllowanceDirectCompilerBoundary : Set where
  constructor pole-quotient-gamma-allowance-direct-compiler-boundary
  field
    genericGammaBoundExistenceIsLive : Bool
    genericGammaBoundExistenceIsLiveIsFalse :
      genericGammaBoundExistenceIsLive ≡ false

    concreteCandidateGammaLineageRecovered : Bool
    concreteCandidateGammaLineageRecoveredIsTrue :
      concreteCandidateGammaLineageRecovered ≡ true

    candidateLineageAlreadyIdentifiedWithFinal8889Producer : Bool
    candidateLineageAlreadyIdentifiedWithFinal8889ProducerIsTrue :
      candidateLineageAlreadyIdentifiedWithFinal8889Producer ≡ true

    gammaDependsOnQuarterPeriodCutoff : Bool
    gammaDependsOnQuarterPeriodCutoffIsFalse :
      gammaDependsOnQuarterPeriodCutoff ≡ false

    exactFinalGammaLeafIsBudgetBelowAssignedAllowance : Bool
    exactFinalGammaLeafIsBudgetBelowAssignedAllowanceIsTrue :
      exactFinalGammaLeafIsBudgetBelowAssignedAllowance ≡ true

    finalGammaAllowancePaymentCompiles : Bool
    finalGammaAllowancePaymentCompilesIsTrue :
      finalGammaAllowancePaymentCompiles ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary :
  PoleQuotientGammaAllowanceDirectCompilerBoundary
canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary =
  pole-quotient-gamma-allowance-direct-compiler-boundary
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    "Do not search for an arbitrary Gamma bound or invent Gamma(J). The vendored exact 8889 PoleQuotientGammaBudget theorem calls gammaConeEnvelope directly, so the epsGamma/gammaConeEnvelope producer identity is source-recovered, and the coarse loss is localized at the stripConst/C2 taper-norm envelope. The terminal analytic theorem remains concrete and unpaid in Agda: on the same universal pole-quotient taper, produce a sharp Gamma payment compatible with the baseline-excess window. Historical identity is no longer a prerequisite; theorem transport and quantitative repair/bypass remain. RH is not derived."
