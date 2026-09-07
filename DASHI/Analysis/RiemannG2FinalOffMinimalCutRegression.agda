module DASHI.Analysis.RiemannG2FinalOffMinimalCutRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Core.TwoChannelAllowanceCompositionExact as Core
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as Minimal
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2PoleQuotientOffChosenCutoffCompilerExact as Chosen
import DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact as WindowBridge
import DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact as FinalOff
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Allowance

------------------------------------------------------------------------
-- Regression: authoritative final Off boundary after carrier/trust minimisation.
------------------------------------------------------------------------

coreAllowanceCompositionOwned :
  Core.TwoChannelAllowanceBoundary.intermediateAllowanceCompositionOwned
    Core.canonicalTwoChannelAllowanceBoundary ≡ true
coreAllowanceCompositionOwned = refl

coreDoesNotChooseAllowance :
  Core.TwoChannelAllowanceBoundary.compilerChoosesIntermediateAllowance
    Core.canonicalTwoChannelAllowanceBoundary ≡ false
coreDoesNotChooseAllowance = refl

leanStatusDoesNotBecomeAgdaProof :
  Transport.ExplicitCutoffNearFarAgdaTransportBoundary.checkedLeanStatusBooleanInhabitsAgdaInequality
    Transport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ false
leanStatusDoesNotBecomeAgdaProof = refl

crossProverTransportStillExplicit :
  Transport.ExplicitCutoffNearFarAgdaTransportBoundary.crossProverSplitFarTransportStillRequired
    Transport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ true
crossProverTransportStillExplicit = refl

onlyNearUpperFreshAfterCutoffTransport :
  Transport.ExplicitCutoffNearFarAgdaTransportBoundary.afterTransportOnlyNearUpperIsFreshBudgetField
    Transport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ true
onlyNearUpperFreshAfterCutoffTransport = refl

allCutoffNearFamilyPruned :
  Chosen.ChosenCutoffOffCompilerBoundary.allCutoffNearBudgetFamilyRequired
    Chosen.canonicalChosenCutoffOffCompilerBoundary ≡ false
allCutoffNearFamilyPruned = refl

oneChosenBudgetSufficient :
  Chosen.ChosenCutoffOffCompilerBoundary.oneChosenNearFarBudgetSufficient
    Chosen.canonicalChosenCutoffOffCompilerBoundary ≡ true
oneChosenBudgetSufficient = refl

routeMetadataNotFinalConsumerRequirement :
  Minimal.SelectedFiniteNearMinimalConsumerBoundary.routeClassificationRequiredByFinalOffConsumer
    Minimal.canonicalSelectedFiniteNearMinimalConsumerBoundary ≡ false
routeMetadataNotFinalConsumerRequirement = refl

sourceOrbitNotFinalConsumerRequirement :
  Minimal.SelectedFiniteNearMinimalConsumerBoundary.sourceOrbitAttachmentRequiredAfterExactWindowAttachment
    Minimal.canonicalSelectedFiniteNearMinimalConsumerBoundary ≡ false
sourceOrbitNotFinalConsumerRequirement = refl

windowBudgetUpperCompilesToTransportedNearUpper :
  WindowBridge.WindowBudgetTransportBoundary.transportedNearUpperIsCompilerOutput
    WindowBridge.canonicalWindowBudgetTransportBoundary ≡ true
windowBudgetUpperCompilesToTransportedNearUpper = refl

noSecondFiniteEvaluation :
  WindowBridge.WindowBudgetTransportBoundary.secondFiniteNearEvaluationRequired
    WindowBridge.canonicalWindowBudgetTransportBoundary ≡ false
noSecondFiniteEvaluation = refl

allCutoffNearUpperFamilyNotRequired :
  FinalOff.TransportedChosenCutoffOffBoundary.allCutoffNearUpperFamilyRequired
    FinalOff.canonicalTransportedChosenCutoffOffBoundary ≡ false
allCutoffNearUpperFamilyNotRequired = refl

chosenNearUpperStillRequired :
  FinalOff.TransportedChosenCutoffOffBoundary.oneChosenNearUpperRequired
    FinalOff.canonicalTransportedChosenCutoffOffBoundary ≡ true
chosenNearUpperStillRequired = refl

farAllowanceReceiptStillRequired :
  FinalOff.TransportedChosenCutoffOffBoundary.farBudgetMustFitIntermediateAllowance
    FinalOff.canonicalTransportedChosenCutoffOffBoundary ≡ true
farAllowanceReceiptStillRequired = refl

nearSlackStillRequired :
  FinalOff.TransportedChosenCutoffOffBoundary.nearBudgetMustLeaveIntermediateAllowance
    FinalOff.canonicalTransportedChosenCutoffOffBoundary ≡ true
nearSlackStillRequired = refl

finalOffPaymentCompilesConditionally :
  FinalOff.TransportedChosenCutoffOffBoundary.finalOffPaymentCompilesAfterTheseReceipts
    FinalOff.canonicalTransportedChosenCutoffOffBoundary ≡ true
finalOffPaymentCompilesConditionally = refl

jointNearFarFitNotOpaqueLeaf :
  Allowance.PoleQuotientOffIntermediateAllowanceBoundary.jointNearPlusFarAllowanceFitIsFreshOpaqueLeaf
    Allowance.canonicalPoleQuotientOffIntermediateAllowanceBoundary ≡ false
jointNearFarFitNotOpaqueLeaf = refl

rhStillOpen :
  FinalOff.TransportedChosenCutoffOffBoundary.rhDerived
    FinalOff.canonicalTransportedChosenCutoffOffBoundary ≡ false
rhStillOpen = refl
