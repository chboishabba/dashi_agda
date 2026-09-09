module DASHI.Analysis.RiemannG2LiteralPhaseJointMarginCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2BalanceFreeComplementContextExact as Context
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Legacy
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- LITERAL PHASE-SUM -> BALANCE-FREE CANONICAL MARGIN
--
-- The analytic theorem is now dependency-level independent of the terminal
-- balance.  Its context contains the scalar/order/taper/cluster coordinates
-- required to STATE the inequality, but no theorem `cluster = Off + Gamma`.
--
-- The research theorem is therefore exactly the visible signed-phase statement:
--
--   literalFiniteNearValue + transportedFar + literalGamma < clusterMargin.
--
-- Rewriting the exact final-near equality produces the canonical joint-margin
-- payment.  Only after that payment exists may a separate final-balance
-- attachment be supplied to compile contradiction.
------------------------------------------------------------------------

record LiteralPhaseJointMarginPayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (model : Literal.FinalPoleNearLiteralModel (Direct.offInput targets))
    (context : Context.BalanceFreeComplementContext targets) : Set₁ where
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
  Context.BalanceFreeJointMarginPayment context
compileLiteralPhaseMarginToCanonicalPayment
  {model = model} payment
  with Literal.finalNearResponseIsLiteralFiniteNear model
... | refl = record
  { Context.strictMargin = literalPhaseStrictBelowMargin payment
  ; Context.paymentReference = paymentReference payment
  }

------------------------------------------------------------------------
-- The final balance is explicitly downstream.  There is intentionally no
-- contradiction compiler taking only LiteralPhaseJointMarginPayment.
------------------------------------------------------------------------

compileLiteralPhasePaymentToLegacyInput :
  forall {S transport targets model context} ->
  (balance : Context.FinalClusterBalanceAttachment context) ->
  LiteralPhaseJointMarginPayment
    {S = S} {transport = transport}
    targets model context ->
  Legacy.DirectIndependentComplementMarginInput targets
compileLiteralPhasePaymentToLegacyInput balance payment =
  Context.compileBalanceFreePaymentToLegacyInput balance
    (compileLiteralPhaseMarginToCanonicalPayment payment)

literalPhasePaymentAndBalanceContradiction :
  forall {S transport targets model context} ->
  Context.FinalClusterBalanceAttachment context ->
  LiteralPhaseJointMarginPayment
    {S = S} {transport = transport}
    targets model context ->
  ⊥
literalPhasePaymentAndBalanceContradiction balance payment =
  Legacy.directIndependentComplementContradiction
    (compileLiteralPhasePaymentToLegacyInput balance payment)

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

    literalPhasePaymentCanAccessFinalClusterBalance : Bool
    literalPhasePaymentCanAccessFinalClusterBalanceIsFalse :
      literalPhasePaymentCanAccessFinalClusterBalance ≡ false

    finalBalanceRequiredOnlyAfterAnalyticPayment : Bool
    finalBalanceRequiredOnlyAfterAnalyticPaymentIsTrue :
      finalBalanceRequiredOnlyAfterAnalyticPayment ≡ true

    secondNearEnvelopeRequired : Bool
    secondNearEnvelopeRequiredIsFalse :
      secondNearEnvelopeRequired ≡ false

    rewritingLiteralSumToFinalNearCreatesNewAnalysis : Bool
    rewritingLiteralSumToFinalNearCreatesNewAnalysisIsFalse :
      rewritingLiteralSumToFinalNearCreatesNewAnalysis ≡ false

    literalPhasePaymentCompilesCanonicalOneLeafMargin : Bool
    literalPhasePaymentCompilesCanonicalOneLeafMarginIsTrue :
      literalPhasePaymentCompilesCanonicalOneLeafMargin ≡ true

    paymentPlusBalanceCompilesContradiction : Bool
    paymentPlusBalanceCompilesContradictionIsTrue :
      paymentPlusBalanceCompilesContradiction ≡ true

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
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The analytic dependency graph is now genuinely balance-free. LiteralPhaseJointMarginPayment is indexed by the exact literal near model and BalanceFreeComplementContext, whose type contains no final cluster=Off+Gamma theorem. Thus the phase+far+Gamma<cluster-margin theorem cannot depend on that final balance through its input context. Its exact final-near equality compiles to BalanceFreeJointMarginPayment. Only afterward is FinalClusterBalanceAttachment supplied to recover the historical final consumer and contradiction. The analytic inequality itself remains unproved and RH is not derived."
