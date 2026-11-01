module DASHI.Analysis.RiemannG2LiteralPhaseDirectClusterResponseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Literal
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as ClusterDirect
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- LITERAL PHASE THEOREM DIRECTLY AGAINST THE ACTUAL CLUSTER RESPONSE
--
-- The intermediate target M_cluster has been eliminated.  On the exact final
-- phase-visible carrier, the only scalar analytic theorem is now
--
--   literalFiniteNearValue + B_far(J) + D_Gamma
--     < ClusterResponse(g_pole).
--
-- The analytic context contains no final cluster balance.  Rewriting the exact
-- final-near equality compiles this theorem to DirectClusterResponsePayment.
-- Only afterward is the downstream balance attachment consumed.
------------------------------------------------------------------------

record LiteralPhaseDirectClusterPayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (model : Literal.FinalPoleNearLiteralModel (Direct.offInput targets))
    (context : ClusterDirect.BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    gamma = Direct.directGammaTarget targets
  field
    literalPhaseBelowClusterResponse :
      Order._<_ (Split.order (ClusterDirect.surface context))
        (Split.add (ClusterDirect.surface context)
          (Existing.cast (ClusterDirect.offScalarIdentity context)
            (NearFar.add S
              (Literal.literalFiniteNearValue model)
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff (Direct.offInput targets)))))
          (Existing.cast (ClusterDirect.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (ClusterDirect.clusterScalarIdentity context)
          (ClusterDirect.ClusterResponse context
            (ClusterDirect.clusterUniversalPoleQuotientTaper context)))

    paymentReference : String

open LiteralPhaseDirectClusterPayment public

compileLiteralPhaseToDirectClusterPayment :
  forall {S transport targets model context} ->
  LiteralPhaseDirectClusterPayment
    {S = S} {transport = transport}
    targets model context ->
  ClusterDirect.DirectClusterResponsePayment context
compileLiteralPhaseToDirectClusterPayment {model = model} payment
  with Literal.finalNearResponseIsLiteralFiniteNear model
... | refl = record
  { ClusterDirect.complementBudgetStrictBelowClusterResponse =
      literalPhaseBelowClusterResponse payment
  ; ClusterDirect.paymentReference = paymentReference payment
  }

literalPhaseDirectClusterContradiction :
  forall {S transport targets model context} ->
  LiteralPhaseDirectClusterPayment
    {S = S} {transport = transport}
    targets model context ->
  ClusterDirect.DirectClusterResponseBalanceAttachment context ->
  ⊥
literalPhaseDirectClusterContradiction payment balance =
  ClusterDirect.directClusterResponseContradiction
    _
    (compileLiteralPhaseToDirectClusterPayment payment)
    balance

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LiteralPhaseDirectClusterBoundary : Set where
  constructor literal-phase-direct-cluster-boundary
  field
    intermediateClusterMarginPrimitive : Bool
    intermediateClusterMarginPrimitiveIsFalse :
      intermediateClusterMarginPrimitive ≡ false

    quantitativeClusterMarginLowerPrimitive : Bool
    quantitativeClusterMarginLowerPrimitiveIsFalse :
      quantitativeClusterMarginLowerPrimitive ≡ false

    analyticPaymentCanAccessFinalBalance : Bool
    analyticPaymentCanAccessFinalBalanceIsFalse :
      analyticPaymentCanAccessFinalBalance ≡ false

    literalPhaseTheoremTargetsActualClusterResponse : Bool
    literalPhaseTheoremTargetsActualClusterResponseIsTrue :
      literalPhaseTheoremTargetsActualClusterResponse ≡ true

    exactNearRewriteCompilesDirectClusterPayment : Bool
    exactNearRewriteCompilesDirectClusterPaymentIsTrue :
      exactNearRewriteCompilesDirectClusterPayment ≡ true

    paymentPlusBalanceCompilesContradiction : Bool
    paymentPlusBalanceCompilesContradictionIsTrue :
      paymentPlusBalanceCompilesContradiction ≡ true

    paymentInhabitedHere : Bool
    paymentInhabitedHereIsFalse : paymentInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalLiteralPhaseDirectClusterBoundary : LiteralPhaseDirectClusterBoundary
canonicalLiteralPhaseDirectClusterBoundary =
  literal-phase-direct-cluster-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The high scalar theorem is now stated on the smallest visible consumer: literal finite-near phase sum plus transported far budget plus literal Gamma response is strictly below the actual same-ordinate ClusterResponse on the universal pole-quotient taper. No intermediate M_cluster or M_cluster<=ClusterResponse theorem is a prerequisite, and the analytic payment cannot access the downstream final balance. Exact final-near rewriting compiles the theorem to the direct cluster-response payment; payment plus balance gives contradiction. The theorem remains unproved and RH is not derived."
