module DASHI.Analysis.RiemannG2GenericNearUpperClusterResponseCompilerExact where

------------------------------------------------------------------------
-- GENERIC FINAL-NEAR UPPER -> ACTUAL CLUSTERRESPONSE PAYMENT
--
-- The terminal certified/high consumer does not care how a near upper U was
-- produced.  It needs only:
--
--   nearResponseAt(J) <= U
--
-- and the independent strict theorem
--
--   cast(U + B_far(J)) + cast(D_Gamma) < cast(ClusterResponse).
--
-- This owner centralizes the monotone lift.  Direct finite certificates,
-- concrete embedded certificates, or cellwise interval enclosures may all feed
-- this same surface without forking the Clay/high architecture.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as Cluster

record FinalNearUpper
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) : Set₁ where
  field
    upperValue : NearFar.Scalar S
    nearResponseBelowUpper :
      NearFar._≤_ S
        (Transport.nearResponseAt transport (Direct.chosenCutoff offInput))
        upperValue
    upperReference : String

open FinalNearUpper public

record GenericNearUpperClusterMargin
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport)
    (nearUpper : FinalNearUpper (Direct.offInput targets))
    (context : Cluster.BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    offInput = Direct.offInput targets
    gamma = Direct.directGammaTarget targets
    U = upperValue nearUpper
  field
    upperEnvelopeStrictBelowCluster :
      Order._<_ (Split.order (Cluster.surface context))
        (Split.add (Cluster.surface context)
          (Existing.cast (Cluster.offScalarIdentity context)
            (NearFar.add S U
              (Transport.farBudgetAt transport
                (Direct.chosenCutoff offInput))))
          (Existing.cast (Cluster.gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (Cluster.clusterScalarIdentity context)
          (Cluster.ClusterResponse context
            (Cluster.clusterUniversalPoleQuotientTaper context)))

    marginReference : String

open GenericNearUpperClusterMargin public

sourceOffBudgetBelowGenericEnvelope :
  forall {S transport targets nearUpper} ->
  NearFar._≤_ S
    (Direct.directOffBudget (Direct.offInput targets)
      (Transport.universalPoleQuotientTaper transport))
    (NearFar.add S
      (upperValue nearUpper)
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))
sourceOffBudgetBelowGenericEnvelope
    {S = S} {transport = transport} {targets = targets}
    {nearUpper = nearUpper} =
  NearFar.addMonotone S
    (nearResponseBelowUpper nearUpper)
    (Direct.sourceOrderReflexive (Direct.offInput targets)
      (Transport.farBudgetAt transport
        (Direct.chosenCutoff (Direct.offInput targets))))

compiledComplementBudgetBelowGenericEnvelope :
  forall {S transport targets nearUpper context} ->
  let gamma = Direct.directGammaTarget targets
      U = upperValue nearUpper
  in Order._≤_ (Split.order (Cluster.surface context))
      (Split.add (Cluster.surface context)
        (Existing.cast (Cluster.offScalarIdentity context)
          (Off.OffOrdinateBudget (Direct.directOffTarget targets)
            (Off.universalPoleQuotientTaper (Direct.directOffTarget targets))))
        (Existing.cast (Cluster.gammaScalarIdentity context)
          (Gamma.GammaBudget gamma
            (Gamma.universalPoleQuotientTaper gamma))))
      (Split.add (Cluster.surface context)
        (Existing.cast (Cluster.offScalarIdentity context)
          (NearFar.add S U
            (Transport.farBudgetAt transport
              (Direct.chosenCutoff (Direct.offInput targets)))))
        (Existing.cast (Cluster.gammaScalarIdentity context)
          (Gamma.GammaBudget gamma
            (Gamma.universalPoleQuotientTaper gamma))))
compiledComplementBudgetBelowGenericEnvelope
    {S = S} {targets = targets} {nearUpper = nearUpper}
    {context = context} =
  Split.addMonotone (Cluster.surface context)
    (Cluster.offOrderTransport context
      (sourceOffBudgetBelowGenericEnvelope
        {S = S} {targets = targets} {nearUpper = nearUpper}))
    (Cluster.compiledGammaUpper context)

compileGenericNearUpperToDirectClusterPayment :
  forall {S transport targets nearUpper context} ->
  GenericNearUpperClusterMargin
    {S = S} {transport = transport}
    targets nearUpper context ->
  Cluster.DirectClusterResponsePayment context
compileGenericNearUpperToDirectClusterPayment
    {context = context} margin = record
  { Cluster.complementBudgetStrictBelowClusterResponse =
      Order.leLtTrans (Split.order (Cluster.surface context))
        compiledComplementBudgetBelowGenericEnvelope
        (upperEnvelopeStrictBelowCluster margin)
  ; Cluster.paymentReference = marginReference margin
  }

record GenericNearUpperClusterBoundary : Set where
  constructor generic-near-upper-cluster-boundary
  field
    terminalClusterCompilerNeedsCertificateImplementation : Bool
    terminalClusterCompilerNeedsCertificateImplementationIsFalse :
      terminalClusterCompilerNeedsCertificateImplementation ≡ false

    oneNearUpperTheoremSufficesForMonotoneLift : Bool
    oneNearUpperTheoremSufficesForMonotoneLiftIsTrue :
      oneNearUpperTheoremSufficesForMonotoneLift ≡ true

    strictUpperEnvelopeBelowClusterStillRequired : Bool
    strictUpperEnvelopeBelowClusterStillRequiredIsTrue :
      strictUpperEnvelopeBelowClusterStillRequired ≡ true

    finalBalanceAvailableToStrictMargin : Bool
    finalBalanceAvailableToStrictMarginIsFalse :
      finalBalanceAvailableToStrictMargin ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGenericNearUpperClusterBoundary : GenericNearUpperClusterBoundary
canonicalGenericNearUpperClusterBoundary =
  generic-near-upper-cluster-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    "Make nearResponseAt(J)<=U the implementation-neutral producer interface. Any theorem-bearing producer of U may feed the same monotone Off/Gamma lift. The only remaining strict analytic theorem is cast(U+B_far)+cast(D_Gamma)<ClusterResponse on the balance-free context. The final balance remains downstream and RH is not derived here."
