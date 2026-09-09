module DASHI.Analysis.RiemannG2LiteralPhaseJointMarginCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2DirectComplementUnpaidContextExact as Context
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Legacy
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- LITERAL PHASE-SUM -> CANONICAL ONE-LEAF MARGIN
--
-- This is now genuinely lower than the final strict-margin input.  The payment
-- is indexed only by:
--
--   * the direct literal targets;
--   * an UNPAID same-object/order/taper/cluster context; and
--   * the final literal near model.
--
-- It does not presuppose `literalComplementStrictBelowMargin` anywhere in its
-- indices.  The analytic theorem is stated directly on the phase-visible finite
-- sum.  Rewriting the exact final-near equality creates the canonical margin
-- payment, which then compiles to the historical final input and contradiction.
------------------------------------------------------------------------

record LiteralPhaseJointMarginPayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (model : Literal.FinalPoleNearLiteralModel (Direct.offInput targets))
    (context : Context.DirectComplementUnpaidContext targets) : Set₁ where
  private
    gamma = Direct.directGammaTarget targets
    cluster0 = Context.cluster context
  field
    literalPhaseStrictBelowMargin :
      Complement._<_ (Split.order (Context.surface context))
        (Split.add (Context.surface context)
          (Existing.cast (Context.offScalarIdentity context)
            (NearFar.add S
              (Literal.literalFiniteNearValue model)
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff (Direct.offInput targets)))))
          (Existing.cast (Context.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (Context.clusterScalarIdentity context)
          (Cluster.ClusterMargin cluster0
            (Cluster.universalPoleQuotientTaper cluster0)))

    paymentReference : String

open LiteralPhaseJointMarginPayment public

compileLiteralPhaseMarginToCanonicalPayment :
  forall {S transport targets model context} ->
  LiteralPhaseJointMarginPayment
    {S = S} {transport = transport}
    targets model context ->
  Context.CanonicalJointMarginPayment context
compileLiteralPhaseMarginToCanonicalPayment
  {model = model} {context = context} payment
  with Literal.finalNearResponseIsLiteralFiniteNear model
... | refl = record
  { Context.literalComplementStrictBelowMargin =
      literalPhaseStrictBelowMargin payment
  ; Context.paymentReference = paymentReference payment
  }

compileLiteralPhasePaymentToLegacyInput :
  forall {S transport targets model context} ->
  LiteralPhaseJointMarginPayment
    {S = S} {transport = transport}
    targets model context ->
  Legacy.DirectIndependentComplementMarginInput targets
compileLiteralPhasePaymentToLegacyInput {context = context} payment =
  Context.compileContextAndPaymentToLegacyInput context
    (compileLiteralPhaseMarginToCanonicalPayment payment)

literalPhasePaymentContradiction :
  forall {S transport targets model context} ->
  LiteralPhaseJointMarginPayment
    {S = S} {transport = transport}
    targets model context ->
  ⊥
literalPhasePaymentContradiction payment =
  Legacy.directIndependentComplementContradiction
    (compileLiteralPhasePaymentToLegacyInput payment)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LiteralPhaseJointMarginBoundary : Set where
  constructor literal-phase-joint-margin-boundary
  field
    analyticTheoremMayBeStatedOnLiteralPhaseSum : Bool
    analyticTheoremMayBeStatedOnLiteralPhaseSumIsTrue :
      analyticTheoremMayBeStatedOnLiteralPhaseSum ≡ true

    literalPhasePaymentPresupposesCanonicalStrictMargin : Bool
    literalPhasePaymentPresupposesCanonicalStrictMarginIsFalse :
      literalPhasePaymentPresupposesCanonicalStrictMargin ≡ false

    secondNearEnvelopeRequired : Bool
    secondNearEnvelopeRequiredIsFalse :
      secondNearEnvelopeRequired ≡ false

    rewritingLiteralSumToFinalNearCreatesNewAnalysis : Bool
    rewritingLiteralSumToFinalNearCreatesNewAnalysisIsFalse :
      rewritingLiteralSumToFinalNearCreatesNewAnalysis ≡ false

    literalPhasePaymentCompilesCanonicalOneLeafMargin : Bool
    literalPhasePaymentCompilesCanonicalOneLeafMarginIsTrue :
      literalPhasePaymentCompilesCanonicalOneLeafMargin ≡ true

    literalPhasePaymentCompilesContradiction : Bool
    literalPhasePaymentCompilesContradictionIsTrue :
      literalPhasePaymentCompilesContradiction ≡ true

    literalPhasePaymentInhabitedHere : Bool
    literalPhasePaymentInhabitedHereIsFalse :
      literalPhasePaymentInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLiteralPhaseJointMarginBoundary :
  LiteralPhaseJointMarginBoundary
canonicalLiteralPhaseJointMarginBoundary =
  literal-phase-joint-margin-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The structural circularity is removed. LiteralPhaseJointMarginPayment is indexed only by the unpaid final context and the exact literal near model; it no longer requires a DirectIndependentComplementMarginInput that already contains the desired strict margin. Prove literalFiniteNearValue + transported far budget + literal Gamma response < quantitative cluster margin on the exact universal pole-quotient carrier. The exact final-near equality compiles that theorem into CanonicalJointMarginPayment, then into the historical final input and contradiction. The analytic inequality itself remains unproved here, so RH is not derived."
