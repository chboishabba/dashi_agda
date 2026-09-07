module DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralResponseNormalizedAnalyticCoresExact as Literal
import DASHI.Analysis.RiemannG2IndependentComplementMarginFinalExact as OneLeaf
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final

------------------------------------------------------------------------
-- AUTHORITATIVE MINIMAL HIGH-ORDINATE POLE-QUOTIENT CUT
--
-- Least-privilege normalization now removes the need to expose separate
-- finite-near and Gamma upper-envelope theorems as primitive terminal leaves.
-- At one selected cutoff J choose
--
--   B_near(J)  := D_near(J),
--   B_off(J)   := D_near(J) + B_far(J),
--   B_Gamma(g) := D_Gamma(g),
--
-- using only source-order reflexivity for the channel upper/allowance fields.
-- The checked far-shell bound remains a genuine independent input.
--
-- The one scalar analytic leaf is therefore
--
--   cast(D_near(J) + B_far(J))
--     + cast(D_Gamma(g_pole))
--       < cast(M_cluster).
--
-- CRITICAL FIREWALL: this compression does not erase the finite-near phase or
-- Gamma mathematics.  They occur literally inside that joint inequality, which
-- must be proved independently of the final
--
--   cluster = Off + Gamma
--
-- balance.  The 8889 budget-circularity no-go therefore remains respected.
--
-- CROSS-PROVER / REPRESENTATION
--   checked-Lean split/far theorem -> Agda transport;
--   source-order reflexivity;
--   source scalar/order/taper identities;
--   final cluster same-object attachment.
--
-- PRUNED AS PRIMITIVE TERMINAL LEAVES
--   separate chosen finite-near upper envelope;
--   separate fresh Gamma envelope upper;
--   intermediate epsilon / Off allowance slack;
--   separate Gamma allowance slack;
--   determinant direct payment;
--   all-cutoff near upper families;
--   rebuilding final contradiction algebra.
------------------------------------------------------------------------

data FinalCutCoordinate : Set where
  transportCheckedLeanSplitFarToAgda : FinalCutCoordinate
  sourceOrderReflexivity : FinalCutCoordinate
  proveIndependentLiteralComplementMargin : FinalCutCoordinate
  transportFinalSourceOrders : FinalCutCoordinate
  attachFinalClusterSameObject : FinalCutCoordinate

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
coordinateClass proveChosenFiniteNearUpper = pruned
coordinateClass proveFreshGammaEnvelope = pruned
coordinateClass proveChosenNearLeavesFarAllowance = pruned
coordinateClass proveGammaFitsAssignedAllowance = pruned
coordinateClass rebuildNearFarBudgetFamilyForEveryCutoff = pruned
coordinateClass recoverDeterminantDirectPayment = pruned
coordinateClass rebuildFinalContradiction = pruned

------------------------------------------------------------------------
-- Exact regression pins against the new least-privilege compilers.
------------------------------------------------------------------------

leanToAgdaTransportIsStillExplicit :
  OffTransport.ExplicitCutoffNearFarAgdaTransportBoundary.crossProverSplitFarTransportStillRequired
    OffTransport.canonicalExplicitCutoffNearFarAgdaTransportBoundary ≡ true
leanToAgdaTransportIsStillExplicit = refl

separateFiniteNearUpperNoLongerPrimitive :
  Literal.LiteralResponseNormalizedBoundary.separateFiniteNearUpperScalarRequired
    Literal.canonicalLiteralResponseNormalizedBoundary ≡ false
separateFiniteNearUpperNoLongerPrimitive = refl

transportedFarShellStillUsed :
  Literal.LiteralResponseNormalizedBoundary.transportedFarShellUpperStillRequired
    Literal.canonicalLiteralResponseNormalizedBoundary ≡ true
transportedFarShellStillUsed = refl

separateGammaEnvelopeNoLongerPrimitive :
  Literal.LiteralResponseNormalizedBoundary.separateGammaEnvelopeScalarRequired
    Literal.canonicalLiteralResponseNormalizedBoundary ≡ false
separateGammaEnvelopeNoLongerPrimitive = refl

oneIndependentComplementMarginIsTerminalScalarLeaf :
  OneLeaf.IndependentComplementMarginBoundary.oneIndependentComplementMarginIsScalarLeaf
    OneLeaf.canonicalIndependentComplementMarginBoundary ≡ true
oneIndependentComplementMarginIsTerminalScalarLeaf = refl

finalBalanceCannotManufactureMargin :
  OneLeaf.IndependentComplementMarginBoundary.finalBalanceMayBeUsedToProveThatMargin
    OneLeaf.canonicalIndependentComplementMarginBoundary ≡ false
finalBalanceCannotManufactureMargin = refl

oneLeafCompilesContradiction :
  OneLeaf.IndependentComplementMarginBoundary.oneLeafCompilesExistingContradiction
    OneLeaf.canonicalIndependentComplementMarginBoundary ≡ true
oneLeafCompilesContradiction = refl

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
    "The terminal scalar API is one independently proved same-case complement inequality: cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster). Separate finite-near and Gamma envelope upper theorems are no longer primitive terminal leaves because their channel budgets may be the literal responses under source-order reflexivity. Their mathematics has not disappeared: target-centred finite-near phase and the literal Gamma response occur inside the joint theorem itself, together with the independently transported far-shell budget. The joint theorem may not be manufactured from cluster=Off+Gamma; that balance remains a downstream same-object representation receipt. With source order/scalar/taper transport, the one scalar leaf compiles the existing contradiction. RH is not derived."
