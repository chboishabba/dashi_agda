module DASHI.Analysis.RiemannG2DirectR2EnvelopeCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- DIRECT R2 ENVELOPE COMPILER
--
-- Current Pareto ownership says the primitive high analytic consumer is
--
--   B_off(J) + D_Gamma(g_pole) < actual ClusterResponse(g_pole)
--
-- on a balance-free context.  A useful producer need not prove that strict
-- inequality in one shot.  It is enough to construct a same-scalar envelope E
-- with
--
--   B_off + D_Gamma <= E
--   E < actual ClusterResponse.
--
-- Then the existing ordered surface's leLtTrans closes the canonical R2
-- payment.  This does NOT reintroduce an intermediate quantitative cluster
-- margin: E is an UPPER envelope for the complement, not a lower surrogate for
-- ClusterResponse.
--
-- The historical 8889 status suggests an O(|t|^-2)-scale producer may be a
-- useful way to inhabit E uniformly at high ordinate, but no inverse-square
-- theorem or coefficient comparison is manufactured here.
------------------------------------------------------------------------

record DirectR2EnvelopeProducer
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : Cluster.BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    envelope : Order.Scalar (Split.order (Cluster.surface context))

    complementBudgetBelowEnvelope :
      Order._≤_ (Split.order (Cluster.surface context))
        (Split.add (Cluster.surface context)
          (Existing.cast (Cluster.offScalarIdentity context)
            (Off.OffOrdinateBudget off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast (Cluster.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        envelope

    envelopeStrictBelowActualClusterResponse :
      Order._<_ (Split.order (Cluster.surface context))
        envelope
        (Existing.cast (Cluster.clusterScalarIdentity context)
          (Cluster.ClusterResponse context
            (Cluster.clusterUniversalPoleQuotientTaper context)))

    envelopeReference : String

open DirectR2EnvelopeProducer public

compileEnvelopeToDirectR2Payment :
  forall {S transport targets context} ->
  DirectR2EnvelopeProducer
    {S = S} {transport = transport} {targets = targets} context ->
  Cluster.DirectClusterResponsePayment context
compileEnvelopeToDirectR2Payment {context = context} producer = record
  { Cluster.complementBudgetStrictBelowClusterResponse =
      Order.leLtTrans
        (Split.order (Cluster.surface context))
        (complementBudgetBelowEnvelope producer)
        (envelopeStrictBelowActualClusterResponse producer)
  ; Cluster.paymentReference = envelopeReference producer
  }

record DirectR2EnvelopeCompilerBoundary : Set where
  constructor direct-r2-envelope-compiler-boundary
  field
    balanceFreeContextReused : Bool
    envelopeTargetsActualClusterResponse : Bool
    complementUpperEnvelopeSuffices : Bool
    finalBalanceAvailableToEnvelopeProducer : Bool
    intermediateQuantitativeClusterMarginReintroduced : Bool
    inverseSquareRateProducerSuggestedByHistoricalStatus : Bool
    inverseSquareRateProducerInhabitedHere : Bool
    directR2PaymentCompiled : Bool
    rhDerived : Bool
open DirectR2EnvelopeCompilerBoundary public

canonicalDirectR2EnvelopeCompilerBoundary : DirectR2EnvelopeCompilerBoundary
canonicalDirectR2EnvelopeCompilerBoundary =
  direct-r2-envelope-compiler-boundary
    true true true false false true false true false

data DirectR2EnvelopeResidual : Set where
  constructUniformHighComplementEnvelope : DirectR2EnvelopeResidual
  proveUniformHighEnvelopeStrictBelowClusterResponse : DirectR2EnvelopeResidual
  instantiateDirectR2EnvelopeProducer : DirectR2EnvelopeResidual

firstDirectR2EnvelopeResidual : DirectR2EnvelopeResidual
firstDirectR2EnvelopeResidual = constructUniformHighComplementEnvelope
