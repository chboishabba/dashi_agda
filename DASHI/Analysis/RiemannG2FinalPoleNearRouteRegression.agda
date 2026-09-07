module DASHI.Analysis.RiemannG2FinalPoleNearRouteRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Analysis.RiemannG2FinalPoleNearRouteReconciliationExact as Route
import DASHI.Analysis.RiemannG2SelectedNearBudgetFinalOffSlackCompilerExact as Slack
import DASHI.Analysis.RiemannG2TargetModulationFinalOffCutoffCompilerExact as Cutoff
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Intermediate

historicalDirectNotFinalCarrier :
  Route.FinalPoleNearRouteBoundary.historicalDirectProducerIsAuthoritativeFinalCarrier
    Route.canonicalFinalPoleNearRouteBoundary ≡ false
historicalDirectNotFinalCarrier = refl

determinantPaymentNotRequired :
  Route.FinalPoleNearRouteBoundary.determinantDirectSignedPaymentRequiredForFinalOff
    Route.canonicalFinalPoleNearRouteBoundary ≡ false
determinantPaymentNotRequired = refl

carrierNeutralProducerPreferred :
  Route.FinalPoleNearRouteBoundary.carrierNeutralFiniteNearProducerIsPreferredDirectProducer
    Route.canonicalFinalPoleNearRouteBoundary ≡ true
carrierNeutralProducerPreferred = refl

secondEvaluationPruned :
  Route.FinalPoleNearRouteBoundary.secondSelectedEvaluationRequiredAfterFiniteNearProducer
    Route.canonicalFinalPoleNearRouteBoundary ≡ false
secondEvaluationPruned = refl

budgetTransportNotFreshAnalysis :
  Route.FinalPoleNearRouteBoundary.selectedBudgetTransportIsFreshHarmonicAnalysis
    Route.canonicalFinalPoleNearRouteBoundary ≡ false
budgetTransportNotFreshAnalysis = refl

selectedEpsilonSlackStillLive :
  Route.FinalPoleNearRouteBoundary.selectedNearBudgetEpsilonSlackStillAnalytic
    Route.canonicalFinalPoleNearRouteBoundary ≡ true
selectedEpsilonSlackStillLive = refl

sourceNativeCutoffPreferred :
  Route.FinalPoleNearRouteBoundary.sourceNativeModulationCutoffIsPreferredJWhenRouteBUsed
    Route.canonicalFinalPoleNearRouteBoundary ≡ true
sourceNativeCutoffPreferred = refl

crossingAlreadyOwnedInFinalInput :
  Cutoff.TargetModulationFinalOffCutoffBoundary.crossingReceiptAlreadyOwnedByFinalInput
    Cutoff.canonicalTargetModulationFinalOffCutoffBoundary ≡ true
crossingAlreadyOwnedInFinalInput = refl

finalNearFarFitCompilerOwned :
  Slack.SelectedNearBudgetFinalOffSlackBoundary.finalNearPlusFarFitCompilesAfterBridge
    Slack.canonicalSelectedNearBudgetFinalOffSlackBoundary ≡ true
finalNearFarFitCompilerOwned = refl

finalOffStillOpen :
  Intermediate.PoleQuotientOffIntermediateAllowanceBoundary.finalOffAllowancePaymentClosed
    Intermediate.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
finalOffStillOpen = refl

rhStillOpen :
  Route.FinalPoleNearRouteBoundary.rhDerived
    Route.canonicalFinalPoleNearRouteBoundary ≡ false
rhStillOpen = refl
