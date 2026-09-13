module DASHI.Analysis.RiemannG2MinimalStrictResponseConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as ClusterDirect
import DASHI.Analysis.RiemannG2LiteralPhaseDirectClusterResponseExact as Phase
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- CONSUMER-MINIMAL STRICT RESPONSE
--
-- The terminal contradiction does not intrinsically consume channel budgets.
-- Its least strict-order input is simply
--
--   OffResponse + GammaResponse < ClusterResponse,
--
-- with the equality ClusterResponse = OffResponse + GammaResponse attached only
-- afterward.  This is a smaller CONSUMER, but it is deliberately not promoted
-- as the preferred acquisition theorem: by itself it hides the finite phase
-- structure needed for proof search.
--
-- The current literal phase+far theorem remains a useful sufficient PRODUCER.
-- Existing channel uppers compile that producer into this minimal consumer.
------------------------------------------------------------------------

record MinimalStrictResponsePayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : ClusterDirect.BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    actualComplementStrictBelowClusterResponse :
      Order._<_ (Split.order (ClusterDirect.surface context))
        (Split.add (ClusterDirect.surface context)
          (Existing.cast (ClusterDirect.offScalarIdentity context)
            (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off)))
          (Existing.cast (ClusterDirect.gammaScalarIdentity context)
            (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (ClusterDirect.clusterScalarIdentity context)
          (ClusterDirect.ClusterResponse context
            (ClusterDirect.clusterUniversalPoleQuotientTaper context)))
    paymentReference : String

open MinimalStrictResponsePayment public

compileBudgetPaymentToMinimalResponse :
  forall {S transport targets context} ->
  ClusterDirect.DirectClusterResponsePayment
    {S = S} {transport = transport} {targets = targets} context ->
  MinimalStrictResponsePayment context
compileBudgetPaymentToMinimalResponse {context = context} payment = record
  { actualComplementStrictBelowClusterResponse =
      Order.leLtTrans (Split.order (ClusterDirect.surface context))
        (ClusterDirect.compiledComplementUpper context)
        (ClusterDirect.complementBudgetStrictBelowClusterResponse payment)
  ; paymentReference = ClusterDirect.paymentReference payment
  }

compileLiteralPhaseToMinimalResponse :
  forall {S transport targets model context} ->
  Phase.LiteralPhaseDirectClusterPayment
    {S = S} {transport = transport} targets model context ->
  MinimalStrictResponsePayment context
compileLiteralPhaseToMinimalResponse payment =
  compileBudgetPaymentToMinimalResponse
    (Phase.compileLiteralPhaseToDirectClusterPayment payment)

minimalStrictResponseContradiction :
  forall {S transport targets context} ->
  MinimalStrictResponsePayment
    {S = S} {transport = transport} {targets = targets} context ->
  ClusterDirect.DirectClusterResponseBalanceAttachment context ->
  ⊥
minimalStrictResponseContradiction {context = context} payment balance
  with ClusterDirect.clusterEqualsOffPlusGamma balance
... | refl =
  Order.ltIrreflexive (Split.order (ClusterDirect.surface context))
    (Existing.cast (ClusterDirect.clusterScalarIdentity context)
      (ClusterDirect.ClusterResponse context
        (ClusterDirect.clusterUniversalPoleQuotientTaper context)))
    (actualComplementStrictBelowClusterResponse payment)

record MinimalStrictResponseBoundary : Set where
  constructor minimal-strict-response-boundary
  field
    terminalConsumerNeedsChannelBudgets : Bool
    terminalConsumerNeedsChannelBudgetsIsFalse :
      terminalConsumerNeedsChannelBudgets ≡ false
    actualComplementStrictnessIsLeastOrderConsumerHere : Bool
    actualComplementStrictnessIsLeastOrderConsumerHereIsTrue :
      actualComplementStrictnessIsLeastOrderConsumerHere ≡ true
    literalPhaseFarTheoremCompilesMinimalConsumer : Bool
    literalPhaseFarTheoremCompilesMinimalConsumerIsTrue :
      literalPhaseFarTheoremCompilesMinimalConsumer ≡ true
    minimalConsumerIsPreferredAcquisitionSurface : Bool
    minimalConsumerIsPreferredAcquisitionSurfaceIsFalse :
      minimalConsumerIsPreferredAcquisitionSurface ≡ false
    reason : String
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalMinimalStrictResponseBoundary : MinimalStrictResponseBoundary
canonicalMinimalStrictResponseBoundary =
  minimal-strict-response-boundary
    false refl
    true refl
    true refl
    false refl
    "Consumer minimization and proof-search acquisition are different. Off+Gamma<ClusterResponse is the least terminal strict-order consumer, but it hides the finite target-centred phase coordinates. Keep literalNear+far+Gamma<ClusterResponse as the preferred sufficient producer because it exposes an independently attackable finite object."
    false refl
