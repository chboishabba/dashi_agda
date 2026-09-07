module DASHI.Analysis.RiemannG2FinalPoleNearRouteReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as HistoricalDirect
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Determinant
import DASHI.Analysis.RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact as Selected
import DASHI.Analysis.RiemannG2SelectedNearBudgetFinalOffSlackCompilerExact as Slack
import DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact as Target
import DASHI.Analysis.RiemannG2PoleNearTargetWindowSpectralIdentificationCompilerExact as Spectral
import DASHI.Analysis.RiemannG2TargetModulationFinalOffCutoffCompilerExact as Cutoff

------------------------------------------------------------------------
-- FINAL-CARRIER FINITE-NEAR ROUTE RECONCILIATION
--
-- The historical DirectFinitePoleNearProducer is richer than the final Off
-- consumer needs. In particular it bundles LiteralTargetCenteredScalarProblem
-- and DirectSignedConsumerPayment, whose canonical problem is the determinant-q
-- G2 scalar lane. That record remains useful as a diagnostic/compatibility donor,
-- but final pole-quotient scheduling must not make its determinant consumer
-- payment a prerequisite.
--
-- The carrier-neutral FiniteNearProducer is the smaller final-facing producer:
--
--   signed evaluation + evaluation budget
--     -> selected same-object attachment / budget transport
--     -> selected near budget + epsilon <= A_off
--     -> final near+far allowance fit.
------------------------------------------------------------------------

data FinalPoleNearRoutePayment : Set where
  recoverCarrierNeutralFiniteNearProducer : FinalPoleNearRoutePayment
  recoverHistoricalDeterminantDirectProducer : FinalPoleNearRoutePayment
  attachFiniteEvaluationToSelectedWindow : FinalPoleNearRoutePayment
  transportSelectedBudgetToFinalNearBudget : FinalPoleNearRoutePayment
  proveSelectedNearBudgetEpsilonSlack : FinalPoleNearRoutePayment
  constructLiteralTargetModulationWindow : FinalPoleNearRoutePayment
  identifyTargetWindowWithModulation : FinalPoleNearRoutePayment
  recoverLawfulExplicitFormulaExtraction : FinalPoleNearRoutePayment


data PaymentState : Set where
  live : PaymentState
  downstream : PaymentState
  compatibility : PaymentState
  conditional : PaymentState

paymentState : FinalPoleNearRoutePayment → PaymentState
paymentState recoverCarrierNeutralFiniteNearProducer = live
paymentState recoverHistoricalDeterminantDirectProducer = compatibility
paymentState attachFiniteEvaluationToSelectedWindow = downstream
paymentState transportSelectedBudgetToFinalNearBudget = downstream
paymentState proveSelectedNearBudgetEpsilonSlack = live
paymentState constructLiteralTargetModulationWindow = conditional
paymentState identifyTargetWindowWithModulation = downstream
paymentState recoverLawfulExplicitFormulaExtraction = conditional

carrierNeutralProducerIsLive :
  paymentState recoverCarrierNeutralFiniteNearProducer ≡ live
carrierNeutralProducerIsLive = refl

historicalDeterminantDirectProducerIsCompatibility :
  paymentState recoverHistoricalDeterminantDirectProducer ≡ compatibility
historicalDeterminantDirectProducerIsCompatibility = refl

selectedAttachmentIsDownstream :
  paymentState attachFiniteEvaluationToSelectedWindow ≡ downstream
selectedAttachmentIsDownstream = refl

selectedBudgetTransportIsDownstream :
  paymentState transportSelectedBudgetToFinalNearBudget ≡ downstream
selectedBudgetTransportIsDownstream = refl

selectedEpsilonSlackIsLive :
  paymentState proveSelectedNearBudgetEpsilonSlack ≡ live
selectedEpsilonSlackIsLive = refl

------------------------------------------------------------------------
-- Existing-owner pins.
------------------------------------------------------------------------

finiteNearProducerAlreadyCarriesBudgetByType : Bool
finiteNearProducerAlreadyCarriesBudgetByType = true

finiteNearProducerAlreadyCarriesBudgetByTypeIsTrue :
  finiteNearProducerAlreadyCarriesBudgetByType ≡ true
finiteNearProducerAlreadyCarriesBudgetByTypeIsTrue = refl

selectedOwnerSaysBudgetExtractionIsNotFreshAnalysis :
  Selected.SelectedFiniteNearSameObjectBoundary.selectedBudgetExtractionNeedsFreshAnalyticEstimateAfterTransport
    Selected.canonicalSelectedFiniteNearSameObjectBoundary ≡ false
selectedOwnerSaysBudgetExtractionIsNotFreshAnalysis = refl

slackOwnerRejectsDeterminantPaymentPrerequisite :
  Slack.SelectedNearBudgetFinalOffSlackBoundary.determinantDirectConsumerPaymentRequiredByThisCompiler
    Slack.canonicalSelectedNearBudgetFinalOffSlackBoundary ≡ false
slackOwnerRejectsDeterminantPaymentPrerequisite = refl

slackOwnerMakesSelectedEpsilonTheoremLive :
  Slack.SelectedNearBudgetFinalOffSlackBoundary.liveAnalyticLeafIsSelectedNearBudgetPlusEpsilonBelowAssigned
    Slack.canonicalSelectedNearBudgetFinalOffSlackBoundary ≡ true
slackOwnerMakesSelectedEpsilonTheoremLive = refl

targetModulationConstructionStillOpen :
  Target.PoleNearTargetModulationBoundary.targetWindowConstructionClosed
    Target.canonicalPoleNearTargetModulationBoundary ≡ false
targetModulationConstructionStillOpen = refl

spectralCompilerDoesNotNeedSecondDecomposition :
  Spectral.PoleNearTargetWindowSpectralIdentificationBoundary.secondSpectralDecompositionTheoremRequired
    Spectral.canonicalPoleNearTargetWindowSpectralIdentificationBoundary ≡ false
spectralCompilerDoesNotNeedSecondDecomposition = refl

sourceNativeCutoffPreferredOverDirectCompatibilityCutoff :
  Cutoff.TargetModulationFinalOffCutoffBoundary.directProducerCutoffIsPreferredSourceOfSelectedJ
    Cutoff.canonicalTargetModulationFinalOffCutoffBoundary ≡ false
sourceNativeCutoffPreferredOverDirectCompatibilityCutoff = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FinalPoleNearRouteBoundary : Set where
  constructor final-pole-near-route-boundary
  field
    historicalDirectProducerIsAuthoritativeFinalCarrier : Bool
    historicalDirectProducerIsAuthoritativeFinalCarrierIsFalse :
      historicalDirectProducerIsAuthoritativeFinalCarrier ≡ false

    determinantDirectSignedPaymentRequiredForFinalOff : Bool
    determinantDirectSignedPaymentRequiredForFinalOffIsFalse :
      determinantDirectSignedPaymentRequiredForFinalOff ≡ false

    carrierNeutralFiniteNearProducerIsPreferredDirectProducer : Bool
    carrierNeutralFiniteNearProducerIsPreferredDirectProducerIsTrue :
      carrierNeutralFiniteNearProducerIsPreferredDirectProducer ≡ true

    secondSelectedEvaluationRequiredAfterFiniteNearProducer : Bool
    secondSelectedEvaluationRequiredAfterFiniteNearProducerIsFalse :
      secondSelectedEvaluationRequiredAfterFiniteNearProducer ≡ false

    selectedBudgetTransportIsFreshHarmonicAnalysis : Bool
    selectedBudgetTransportIsFreshHarmonicAnalysisIsFalse :
      selectedBudgetTransportIsFreshHarmonicAnalysis ≡ false

    selectedNearBudgetEpsilonSlackStillAnalytic : Bool
    selectedNearBudgetEpsilonSlackStillAnalyticIsTrue :
      selectedNearBudgetEpsilonSlackStillAnalytic ≡ true

    explicitFormulaRouteHasMoreUninhabitedPrerequisites : Bool
    explicitFormulaRouteHasMoreUninhabitedPrerequisitesIsTrue :
      explicitFormulaRouteHasMoreUninhabitedPrerequisites ≡ true

    sourceNativeModulationCutoffIsPreferredJWhenRouteBUsed : Bool
    sourceNativeModulationCutoffIsPreferredJWhenRouteBUsedIsTrue :
      sourceNativeModulationCutoffIsPreferredJWhenRouteBUsed ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalPoleNearRouteBoundary : FinalPoleNearRouteBoundary
canonicalFinalPoleNearRouteBoundary =
  final-pole-near-route-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "On the authoritative universal pole-quotient carrier, prefer the carrier-neutral FiniteNearProducer rather than the historical DirectFinitePoleNearProducer whose consumer package is indexed by the determinant-q LiteralTargetCenteredScalarProblem. A FiniteNearProducer already carries one signed evaluation and one budget; after same-object selected attachment and one order/scalar transport, the live scalar theorem is selectedNearBudget + epsilon <= A_off at the common cutoff. The explicit-formula route remains logically admissible but still has more uninhabited producer/extraction prerequisites; if used, take J from PoleNearTargetModulation itself. The determinant direct payment is not promoted and RH remains open."
