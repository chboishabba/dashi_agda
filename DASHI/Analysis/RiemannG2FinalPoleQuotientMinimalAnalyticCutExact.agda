module DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2TransportedChosenCutoffOffAllowanceCompilerExact as Off
import DASHI.Analysis.RiemannG2WindowBudgetToTransportedNearUpperExact as WindowNear
import DASHI.Analysis.RiemannG2SelectedFiniteNearBudgetMinimalConsumerExact as NearPayment
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as Gamma
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final

------------------------------------------------------------------------
-- AUTHORITATIVE MINIMAL HIGH-ORDINATE POLE-QUOTIENT CUT
--
-- This owner distinguishes three kinds of remaining coordinates:
--
--   ANALYTIC
--     Off:   one finite-near upper at the chosen cutoff J, strong enough that
--            the resulting B_near(J) leaves the selected epsilon allowance.
--     Gamma: one same-g_pole Gamma envelope and its assigned allowance fit.
--
--   CROSS-PROVER / REPRESENTATION
--     transport the already-checked Lean every-J split/far theorem into Agda;
--     identify the target-window value/budget with the transported J-coordinates;
--     carry source orders/same-object identities into the final assembly.
--
--   COMPILER OUTPUT
--     NearFarOffOrdinateBudget at chosen J;
--     B_near+B_far <= A_off;
--     final Off/Gamma allowance payments;
--     strict combined-budget contradiction after cluster/order attachment.
--
-- No status Boolean, historical producer name, determinant payment, source-orbit
-- metadata, or all-J near-budget family is promoted into an analytic proof.
------------------------------------------------------------------------

data FinalCutCoordinate : Set where
  transportCheckedLeanSplitFarToAgda : FinalCutCoordinate
  proveChosenFiniteNearUpper : FinalCutCoordinate
  proveChosenNearLeavesFarAllowance : FinalCutCoordinate
  proveFreshSameTaperGammaEnvelope : FinalCutCoordinate
  proveGammaFitsAssignedAllowance : FinalCutCoordinate
  identifyWindowWithTransportedNearCoordinates : FinalCutCoordinate
  transportFinalSourceOrders : FinalCutCoordinate
  attachFinalClusterSameObject : FinalCutCoordinate
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
coordinateClass proveChosenNearLeavesFarAllowance = analytic
coordinateClass proveFreshSameTaperGammaEnvelope = analytic
coordinateClass proveGammaFitsAssignedAllowance = analytic
coordinateClass identifyWindowWithTransportedNearCoordinates = crossProverRepresentation
coordinateClass transportFinalSourceOrders = downstream
coordinateClass attachFinalClusterSameObject = downstream
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

allCutoffNearUpperFamilyPruned :
  Off.TransportedChosenCutoffOffBoundary.allCutoffNearUpperFamilyRequired
    Off.canonicalTransportedChosenCutoffOffBoundary ≡ false
allCutoffNearUpperFamilyPruned = refl

finalOffPaymentCompiles :
  Off.TransportedChosenCutoffOffBoundary.finalOffPaymentCompilesAfterTheseReceipts
    Off.canonicalTransportedChosenCutoffOffBoundary ≡ true
finalOffPaymentCompiles = refl

freshGammaRouteHasNoHistoricalIdentityPrerequisite :
  Gamma.FreshSameTaperGammaEnvelopeBoundary.historical8889IdentityRequiredForFreshEnvelope
    Gamma.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ false
freshGammaRouteHasNoHistoricalIdentityPrerequisite = refl

freshGammaPaymentCompiles :
  Gamma.FreshSameTaperGammaEnvelopeBoundary.freshEnvelopeAllowanceFitCompilesFinalPayment
    Gamma.canonicalFreshSameTaperGammaEnvelopeBoundary ≡ true
freshGammaPaymentCompiles = refl

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

    offNearAllowanceSlackIsAnalyticRequirement : Bool
    offNearAllowanceSlackIsAnalyticRequirementIsTrue :
      offNearAllowanceSlackIsAnalyticRequirement ≡ true

    leanSplitFarTransportIsNewHarmonicAnalysis : Bool
    leanSplitFarTransportIsNewHarmonicAnalysisIsFalse :
      leanSplitFarTransportIsNewHarmonicAnalysis ≡ false

    gammaFreshSameTaperEnvelopeIsAnalyticRequirement : Bool
    gammaFreshSameTaperEnvelopeIsAnalyticRequirementIsTrue :
      gammaFreshSameTaperEnvelopeIsAnalyticRequirement ≡ true

    gammaAssignedAllowanceFitIsAnalyticRequirement : Bool
    gammaAssignedAllowanceFitIsAnalyticRequirementIsTrue :
      gammaAssignedAllowanceFitIsAnalyticRequirement ≡ true

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
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "The authoritative high-ordinate final carrier has two independent analytic channels. Off requires one finite-near upper at the one chosen crossing cutoff and enough near slack to leave an intermediate far allowance; the already-checked Lean split/far theorem still needs proof-bearing Agda transport, but that is a cross-prover trust/representation obligation rather than new harmonic analysis. Gamma requires a theorem-bearing same-g_pole envelope and its assigned-allowance fit; historical 8889 identity is optional route provenance, not the fresh theorem API. Window/transport same-object identities and final source-order/cluster attachment remain representation/downstream work. All-cutoff near families, determinant direct payments, source-orbit terminal dependencies and rebuilding the contradiction are pruned. RH is not derived."
