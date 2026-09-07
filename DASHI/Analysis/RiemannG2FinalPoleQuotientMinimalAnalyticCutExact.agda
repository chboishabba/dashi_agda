module DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact as WindowNear
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as NearPayment
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as Gamma
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final
import DASHI.Analysis.RiemannG2BudgetNormalizedAnalyticCoresExact as Normalized

------------------------------------------------------------------------
-- AUTHORITATIVE MINIMAL HIGH-ORDINATE POLE-QUOTIENT CUT
--
-- Allowance normalization removes two arbitrary slack variables.  Choose
--
--   A_off   := actual selected Off producer budget,
--   A_Gamma := actual Gamma producer budget.
--
-- Then the per-channel core fits are self-order receipts and the only genuinely
-- quantitative compatibility theorem is the literal joint strict margin for the
-- two actual budgets.
--
-- ANALYTIC
--   Off:   one proof-bearing finite-near upper at the selected cutoff J.
--   Gamma: one proof-bearing fresh Gamma response upper on the chosen taper.
--   Joint: actual B_off(J) + B_Gamma(g) is strictly below the final cluster
--          margin after the declared scalar/order transports.
--
-- CROSS-PROVER / REPRESENTATION
--   checked-Lean split/far theorem -> Agda transport;
--   exact selected-window value/budget/order weld;
--   source self-order receipts used by the normalized core constructors;
--   final source-order/taper/cluster same-object attachment.
--
-- PRUNED
--   intermediate epsilon / separate Off allowance slack;
--   separate Gamma allowance slack;
--   determinant direct payment;
--   source-orbit metadata after exact window attachment;
--   all-cutoff near upper family;
--   rebuilding final contradiction algebra.
--
-- No theorem below is manufactured by a status Boolean.
------------------------------------------------------------------------

data FinalCutCoordinate : Set where
  transportCheckedLeanSplitFarToAgda : FinalCutCoordinate
  proveChosenFiniteNearUpper : FinalCutCoordinate
  proveFreshGammaEnvelope : FinalCutCoordinate
  proveActualTwoBudgetStrictMargin : FinalCutCoordinate
  sourceBudgetSelfOrder : FinalCutCoordinate
  identifyWindowWithTransportedNearCoordinates : FinalCutCoordinate
  transportFinalSourceOrders : FinalCutCoordinate
  attachFinalClusterSameObject : FinalCutCoordinate

  proveChosenNearLeavesFarAllowance : FinalCutCoordinate
  proveGammaFitsAssignedAllowance : FinalCutCoordinate
  rebuildNearFarBudgetFamilyForEveryCutoff : FinalCutCoordinate
  recoverDeterminantDirectPayment : FinalCutCoordinate
  recoverSourceOrbitForTerminalNearConsumer : FinalCutCoordinate
  rebuildFinalContradiction : FinalCutCoordinate


data CoordinateClass : Set where
  analytic : CoordinateClass
  crossProverRepresentation : CoordinateClass
  downstream : CoordinateClass
  pruned : CoordinateClass

coordinateClass : FinalCutCoordinate -> CoordinateClass
coordinateClass transportCheckedLeanSplitFarToAgda = crossProverRepresentation
coordinateClass proveChosenFiniteNearUpper = analytic
coordinateClass proveFreshGammaEnvelope = analytic
coordinateClass proveActualTwoBudgetStrictMargin = analytic
coordinateClass sourceBudgetSelfOrder = crossProverRepresentation
coordinateClass identifyWindowWithTransportedNearCoordinates = crossProverRepresentation
coordinateClass transportFinalSourceOrders = downstream
coordinateClass attachFinalClusterSameObject = downstream
coordinateClass proveChosenNearLeavesFarAllowance = pruned
coordinateClass proveGammaFitsAssignedAllowance = pruned
coordinateClass rebuildNearFarBudgetFamilyForEveryCutoff = pruned
coordinateClass recoverDeterminantDirectPayment = pruned
coordinateClass recoverSourceOrbitForTerminalNearConsumer = pruned
coordinateClass rebuildFinalContradiction = pruned

------------------------------------------------------------------------
-- Exact regression pins against the compiler owners.
------------------------------------------------------------------------

leanToAgdaTransportIsStillExplicit :
  OffTransport.ExplicitCutoffNearFarAgdaTransportBoundary.crossProverSplitFarTransportStillRequired
    OffTransport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ true
leanToAgdaTransportIsStillExplicit = refl

onlyChosenNearUpperNeededAfterTransport :
  OffTransport.ExplicitCutoffNearFarAgdaTransportBoundary.afterTransportOnlyNearUpperIsFreshBudgetField
    OffTransport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ true
onlyChosenNearUpperNeededAfterTransport = refl

windowNearUpperIsTransportCompilerOutput :
  WindowNear.WindowBudgetTransportBoundary.transportedNearUpperIsCompilerOutput
    WindowNear.canonicalWindowBudgetTransportBoundary ≡ true
windowNearUpperIsTransportCompilerOutput = refl

sourceOrbitNotTerminalNearRequirement :
  NearPayment.SelectedFiniteNearMinimalConsumerBoundary.sourceOrbitAttachmentRequiredAfterExactWindowAttachment
    NearPayment.canonicalSelectedFiniteNearMinimalConsumerBoundary ≡ false
sourceOrbitNotTerminalNearRequirement = refl

freshGammaRouteHasNoHistoricalIdentityPrerequisite :
  Gamma.FreshSameTaperGammaEnvelopeBoundary.historical8889IdentityRequiredForFreshEnvelope
    Gamma.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
freshGammaRouteHasNoHistoricalIdentityPrerequisite = refl

offSeparateAllowanceSlackPruned :
  Normalized.BudgetNormalizedAnalyticCoreBoundary.offSeparateAssignedAllowanceSlackRequired
    Normalized.canonicalBudgetNormalizedAnalyticCoreBoundary ≡ false
offSeparateAllowanceSlackPruned = refl

gammaSeparateAllowanceSlackPruned :
  Normalized.BudgetNormalizedAnalyticCoreBoundary.gammaSeparateAssignedAllowanceSlackRequired
    Normalized.canonicalBudgetNormalizedAnalyticCoreBoundary ≡ false
gammaSeparateAllowanceSlackPruned = refl

actualTwoBudgetMarginRemains :
  Normalized.BudgetNormalizedAnalyticCoreBoundary.actualTwoBudgetStrictMarginRemainsNontrivial
    Normalized.canonicalBudgetNormalizedAnalyticCoreBoundary ≡ true
actualTwoBudgetMarginRemains = refl

finalOrderTransportCompilesContradiction :
  Final.FinalOrderTransportBoundary.orderTransportPackageCompilesContradiction
    Final.canonicalFinalOrderTransportBoundary ≡ true
finalOrderTransportCompilesContradiction = refl

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record FinalPoleQuotientMinimalAnalyticCutBoundary : Set where
  constructor final-pole-quotient-minimal-analytic-cut-boundary
  field
    offAllCutoffNearFamilyIsAnalyticRequirement : Bool
    offAllCutoffNearFamilyIsAnalyticRequirementIsFalse :
      offAllCutoffNearFamilyIsAnalyticRequirement ≡ false

    offChosenNearUpperIsAnalyticRequirement : Bool
    offChosenNearUpperIsAnalyticRequirementIsTrue :
      offChosenNearUpperIsAnalyticRequirement ≡ true

    offSeparateAllowanceSlackIsAnalyticRequirement : Bool
    offSeparateAllowanceSlackIsAnalyticRequirementIsFalse :
      offSeparateAllowanceSlackIsAnalyticRequirement ≡ false

    leanSplitFarTransportIsNewHarmonicAnalysis : Bool
    leanSplitFarTransportIsNewHarmonicAnalysisIsFalse :
      leanSplitFarTransportIsNewHarmonicAnalysis ≡ false

    gammaFreshEnvelopeUpperIsAnalyticRequirement : Bool
    gammaFreshEnvelopeUpperIsAnalyticRequirementIsTrue :
      gammaFreshEnvelopeUpperIsAnalyticRequirement ≡ true

    gammaSeparateAssignedAllowanceFitIsAnalyticRequirement : Bool
    gammaSeparateAssignedAllowanceFitIsAnalyticRequirementIsFalse :
      gammaSeparateAssignedAllowanceFitIsAnalyticRequirement ≡ false

    actualTwoBudgetStrictMarginIsAnalyticRequirement : Bool
    actualTwoBudgetStrictMarginIsAnalyticRequirementIsTrue :
      actualTwoBudgetStrictMarginIsAnalyticRequirement ≡ true

    sourceBudgetSelfOrderIsNewHarmonicAnalysis : Bool
    sourceBudgetSelfOrderIsNewHarmonicAnalysisIsFalse :
      sourceBudgetSelfOrderIsNewHarmonicAnalysis ≡ false

    channelAllowancesCanBeNormalizedToActualBudgets : Bool
    channelAllowancesCanBeNormalizedToActualBudgetsIsTrue :
      channelAllowancesCanBeNormalizedToActualBudgets ≡ true

    determinantDirectPaymentIsFinalCarrierRequirement : Bool
    determinantDirectPaymentIsFinalCarrierRequirementIsFalse :
      determinantDirectPaymentIsFinalCarrierRequirement ≡ false

    sourceOrbitIsTerminalNearRequirement : Bool
    sourceOrbitIsTerminalNearRequirementIsFalse :
      sourceOrbitIsTerminalNearRequirement ≡ false

    downstreamContradictionNeedsFreshAnalyticProof : Bool
    downstreamContradictionNeedsFreshAnalyticProofIsFalse :
      downstreamContradictionNeedsFreshAnalyticProof ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalPoleQuotientMinimalAnalyticCutBoundary :
  FinalPoleQuotientMinimalAnalyticCutBoundary
canonicalFinalPoleQuotientMinimalAnalyticCutBoundary =
  final-pole-quotient-minimal-analytic-cut-boundary
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Normalize A_off and A_Gamma to the actual producer budgets. The scalar analytic cut is then: one selected finite-near upper for Off, one fresh Gamma response upper, and one strict final margin for the sum of those actual budgets. Separate Off near-slack/intermediate-epsilon and Gamma allowance-fit theorems are bookkeeping decompositions and are pruned. Source-order self-relations, Lean-to-Agda split/far transport, exact window transport, and final same-object/order/cluster welds remain explicit representation receipts. Determinant payment, source-orbit terminal ancestry, all-cutoff near families, and contradiction rebuilding remain pruned. RH is not derived."
