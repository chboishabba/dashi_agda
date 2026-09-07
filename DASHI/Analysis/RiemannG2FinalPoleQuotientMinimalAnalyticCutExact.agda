module DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Margin

------------------------------------------------------------------------
-- AUTHORITATIVE MINIMAL HIGH-ORDINATE POLE-QUOTIENT CUT
--
-- The canonical route now bypasses the historical consumer-assigned allowance
-- layer entirely.  At one selected cutoff J use the literal direct budgets
--
--   B_off(J)   := D_near(J) + B_far(J),
--   B_Gamma(g) := D_Gamma(g),
--
-- where the Off upper is compiler output from the checked near/far split,
-- source-order reflexivity on D_near, and the transported far-shell upper; the
-- Gamma upper is source-order reflexivity.
--
-- The ONE scalar analytic leaf is therefore
--
--   cast(D_near(J) + B_far(J))
--     + cast(D_Gamma(g_pole))
--       < cast(M_cluster).
--
-- CRITICAL FIREWALL: finite-near phase and Gamma mathematics have not vanished.
-- They occur literally inside this joint inequality, which must be proved
-- independently of the downstream same-object balance
--
--   cluster = Off + Gamma.
--
-- Thus the 8889 budget-circularity no-go remains respected. No producer chooses
-- a downstream consumer allowance on this route.
------------------------------------------------------------------------

data FinalCutCoordinate : Set where
  transportCheckedLeanSplitFarToAgda : FinalCutCoordinate
  sourceOrderReflexivity : FinalCutCoordinate
  proveIndependentLiteralComplementMargin : FinalCutCoordinate
  transportFinalSourceOrders : FinalCutCoordinate
  attachFinalClusterSameObject : FinalCutCoordinate

  assignConsumerChannelAllowances : FinalCutCoordinate
  proveChosenFiniteNearUpper : FinalCutCoordinate
  proveFreshGammaEnvelope : FinalCutCoordinate
  proveChosenNearLeavesFarAllowance : FinalCutCoordinate
  proveGammaFitsAssignedAllowance : FinalCutCoordinate
  rebuildNearFarBudgetFamilyForEveryCutoff : FinalCutCoordinate
  recoverDeterminantDirectPayment : FinalCutCoordinate
  rebuildFinalContradiction : FinalCutCoordinate


data CoordinateClass : Set where
  analytic : CoordinateClass
  crossProverRepresentation : CoordinateClass
  downstream : CoordinateClass
  pruned : CoordinateClass

coordinateClass : FinalCutCoordinate -> CoordinateClass
coordinateClass transportCheckedLeanSplitFarToAgda = crossProverRepresentation
coordinateClass sourceOrderReflexivity = crossProverRepresentation
coordinateClass proveIndependentLiteralComplementMargin = analytic
coordinateClass transportFinalSourceOrders = downstream
coordinateClass attachFinalClusterSameObject = downstream
coordinateClass assignConsumerChannelAllowances = pruned
coordinateClass proveChosenFiniteNearUpper = pruned
coordinateClass proveFreshGammaEnvelope = pruned
coordinateClass proveChosenNearLeavesFarAllowance = pruned
coordinateClass proveGammaFitsAssignedAllowance = pruned
coordinateClass rebuildNearFarBudgetFamilyForEveryCutoff = pruned
coordinateClass recoverDeterminantDirectPayment = pruned
coordinateClass rebuildFinalContradiction = pruned

------------------------------------------------------------------------
-- Exact regression pins against the direct least-privilege compilers.
------------------------------------------------------------------------

leanToAgdaTransportIsStillExplicit :
  OffTransport.ExplicitCutoffNearFarAgdaTransportBoundary.crossProverSplitFarTransportStillRequired
    OffTransport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ true
leanToAgdaTransportIsStillExplicit = refl

consumerAllowanceLayerPruned :
  Margin.DirectIndependentComplementMarginBoundary.consumerAssignedAllowanceLayerRequired
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ false
consumerAllowanceLayerPruned = refl

producerDoesNotChooseDownstreamAllowance :
  Margin.DirectIndependentComplementMarginBoundary.producerChoosesDownstreamAllowance
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ false
producerDoesNotChooseDownstreamAllowance = refl

separateFiniteNearUpperNoLongerPrimitive :
  Direct.DirectLiteralComplementTargetBoundary.separateFiniteNearEnvelopeRequired
    Direct.canonicalDirectLiteralComplementTargetBoundary ≡ false
separateFiniteNearUpperNoLongerPrimitive = refl

transportedFarShellStillUsed :
  Direct.DirectLiteralComplementTargetBoundary.transportedFarShellUpperStillUsed
    Direct.canonicalDirectLiteralComplementTargetBoundary ≡ true
transportedFarShellStillUsed = refl

separateGammaEnvelopeNoLongerPrimitive :
  Direct.DirectLiteralComplementTargetBoundary.separateGammaEnvelopeRequired
    Direct.canonicalDirectLiteralComplementTargetBoundary ≡ false
separateGammaEnvelopeNoLongerPrimitive = refl

oneIndependentComplementMarginIsTerminalScalarLeaf :
  Margin.DirectIndependentComplementMarginBoundary.oneIndependentJointMarginIsScalarLeaf
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ true
oneIndependentComplementMarginIsTerminalScalarLeaf = refl

finalBalanceCannotManufactureMargin :
  Margin.DirectIndependentComplementMarginBoundary.finalBalanceMayManufactureJointMargin
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ false
finalBalanceCannotManufactureMargin = refl

directOneLeafCompilesContradiction :
  Margin.DirectIndependentComplementMarginBoundary.directSplitCompilerProducesContradiction
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ true
directOneLeafCompilesContradiction = refl

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record FinalPoleQuotientMinimalAnalyticCutBoundary : Set where
  constructor final-pole-quotient-minimal-analytic-cut-boundary
  field
    consumerAssignedAllowanceLayerIsCanonicalRequirement : Bool
    consumerAssignedAllowanceLayerIsCanonicalRequirementIsFalse :
      consumerAssignedAllowanceLayerIsCanonicalRequirement ≡ false

    separateChosenFiniteNearUpperIsPrimitiveAnalyticRequirement : Bool
    separateChosenFiniteNearUpperIsPrimitiveAnalyticRequirementIsFalse :
      separateChosenFiniteNearUpperIsPrimitiveAnalyticRequirement ≡ false

    separateFreshGammaEnvelopeIsPrimitiveAnalyticRequirement : Bool
    separateFreshGammaEnvelopeIsPrimitiveAnalyticRequirementIsFalse :
      separateFreshGammaEnvelopeIsPrimitiveAnalyticRequirement ≡ false

    independentLiteralComplementMarginIsAnalyticRequirement : Bool
    independentLiteralComplementMarginIsAnalyticRequirementIsTrue :
      independentLiteralComplementMarginIsAnalyticRequirement ≡ true

    literalFiniteNearPhaseStillOccursInJointTheorem : Bool
    literalFiniteNearPhaseStillOccursInJointTheoremIsTrue :
      literalFiniteNearPhaseStillOccursInJointTheorem ≡ true

    literalGammaResponseStillOccursInJointTheorem : Bool
    literalGammaResponseStillOccursInJointTheoremIsTrue :
      literalGammaResponseStillOccursInJointTheorem ≡ true

    transportedFarShellStillOccursInJointTheorem : Bool
    transportedFarShellStillOccursInJointTheoremIsTrue :
      transportedFarShellStillOccursInJointTheorem ≡ true

    leanSplitFarTransportIsNewHarmonicAnalysis : Bool
    leanSplitFarTransportIsNewHarmonicAnalysisIsFalse :
      leanSplitFarTransportIsNewHarmonicAnalysis ≡ false

    sourceOrderReflexivityIsNewHarmonicAnalysis : Bool
    sourceOrderReflexivityIsNewHarmonicAnalysisIsFalse :
      sourceOrderReflexivityIsNewHarmonicAnalysis ≡ false

    finalBalanceMayManufactureAnalyticMargin : Bool
    finalBalanceMayManufactureAnalyticMarginIsFalse :
      finalBalanceMayManufactureAnalyticMargin ≡ false

    determinantDirectPaymentIsFinalCarrierRequirement : Bool
    determinantDirectPaymentIsFinalCarrierRequirementIsFalse :
      determinantDirectPaymentIsFinalCarrierRequirement ≡ false

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
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The canonical high scalar cut is allowance-free and has one analytic theorem: independently prove cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster). Off's source upper is compiled from the checked split, D_near reflexivity, and the transported far upper; Gamma's source upper is reflexivity. Separate near/Gamma envelope theorems and channel allowances are not primitive terminal leaves. Their mathematics remains literally inside the joint theorem. The final cluster=Off+Gamma balance may not manufacture that theorem. With scalar/order/taper/cluster same-object transport, the direct split-complement compiler yields contradiction. RH is not derived."
