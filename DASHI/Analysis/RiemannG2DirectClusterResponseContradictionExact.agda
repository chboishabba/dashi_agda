module DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Order
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

record BalanceFreeClusterResponseContext
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    surface : Split.OrderedAdditiveComplementSurface
    ClusterTaper : Set
    ClusterScalar : Set
    ClusterResponse : ClusterTaper -> ClusterScalar
    clusterUniversalPoleQuotientTaper : ClusterTaper
    offScalarIdentity : Off.Scalar off ≡ Order.Scalar (Split.order surface)
    gammaScalarIdentity : Gamma.Scalar gamma ≡ Order.Scalar (Split.order surface)
    clusterScalarIdentity : ClusterScalar ≡ Order.Scalar (Split.order surface)
    offGammaTaperCarrierIdentity : Off.Taper off ≡ Gamma.Taper gamma
    offClusterTaperCarrierIdentity : Off.Taper off ≡ ClusterTaper
    sameUniversalTaperOffGamma :
      Existing.cast offGammaTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Gamma.universalPoleQuotientTaper gamma
    sameUniversalTaperOffCluster :
      Existing.cast offClusterTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ clusterUniversalPoleQuotientTaper
    offOrderTransport :
      {x y : Off.Scalar off} ->
      Off._≤_ off x y ->
      Order._≤_ (Split.order surface)
        (Existing.cast offScalarIdentity x)
        (Existing.cast offScalarIdentity y)
    gammaOrderTransport :
      {x y : Gamma.Scalar gamma} ->
      Gamma._≤_ gamma x y ->
      Order._≤_ (Split.order surface)
        (Existing.cast gammaScalarIdentity x)
        (Existing.cast gammaScalarIdentity y)
    contextReference : String

open BalanceFreeClusterResponseContext public

record DirectClusterResponsePayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    complementBudgetStrictBelowClusterResponse :
      Order._<_ (Split.order (surface context))
        (Split.add (surface context)
          (Existing.cast (offScalarIdentity context)
            (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off)))
          (Existing.cast (gammaScalarIdentity context)
            (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (clusterScalarIdentity context)
          (ClusterResponse context (clusterUniversalPoleQuotientTaper context)))
    paymentReference : String

open DirectClusterResponsePayment public

record DirectClusterResponseBalanceAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : BalanceFreeClusterResponseContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    clusterEqualsOffPlusGamma :
      Existing.cast (clusterScalarIdentity context)
        (ClusterResponse context (clusterUniversalPoleQuotientTaper context))
      ≡ Split.add (surface context)
          (Existing.cast (offScalarIdentity context)
            (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off)))
          (Existing.cast (gammaScalarIdentity context)
            (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma)))
    balanceReference : String

open DirectClusterResponseBalanceAttachment public

compiledOffUpper :
  forall {S transport targets} ->
  (context : BalanceFreeClusterResponseContext {S = S} {transport = transport} targets) ->
  let off = Direct.directOffTarget targets
  in Order._≤_ (Split.order (surface context))
      (Existing.cast (offScalarIdentity context)
        (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off)))
      (Existing.cast (offScalarIdentity context)
        (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off)))
compiledOffUpper {targets = targets} context =
  offOrderTransport context (Off.signedOffOrdinateUpper (Direct.directOffTarget targets))

compiledGammaUpper :
  forall {S transport targets} ->
  (context : BalanceFreeClusterResponseContext {S = S} {transport = transport} targets) ->
  let gamma = Direct.directGammaTarget targets
  in Order._≤_ (Split.order (surface context))
      (Existing.cast (gammaScalarIdentity context)
        (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma)))
      (Existing.cast (gammaScalarIdentity context)
        (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma)))
compiledGammaUpper {targets = targets} context =
  gammaOrderTransport context (Gamma.gammaResponseUpper (Direct.directGammaTarget targets))

compiledComplementUpper :
  forall {S transport targets} ->
  (context : BalanceFreeClusterResponseContext {S = S} {transport = transport} targets) ->
  let off = Direct.directOffTarget targets
      gamma = Direct.directGammaTarget targets
  in Order._≤_ (Split.order (surface context))
      (Split.add (surface context)
        (Existing.cast (offScalarIdentity context)
          (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off)))
        (Existing.cast (gammaScalarIdentity context)
          (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma))))
      (Split.add (surface context)
        (Existing.cast (offScalarIdentity context)
          (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off)))
        (Existing.cast (gammaScalarIdentity context)
          (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma))))
compiledComplementUpper context =
  Split.addMonotone (surface context)
    (compiledOffUpper context)
    (compiledGammaUpper context)

directClusterResponseContradiction :
  forall {S transport targets} ->
  (context : BalanceFreeClusterResponseContext {S = S} {transport = transport} targets) ->
  DirectClusterResponsePayment context ->
  DirectClusterResponseBalanceAttachment context ->
  ⊥
directClusterResponseContradiction context payment balance
  with clusterEqualsOffPlusGamma balance
... | refl =
  Order.ltIrreflexive (Split.order (surface context))
    (Existing.cast (clusterScalarIdentity context)
      (ClusterResponse context (clusterUniversalPoleQuotientTaper context)))
    (Order.leLtTrans (Split.order (surface context))
      (compiledComplementUpper context)
      (complementBudgetStrictBelowClusterResponse payment))

record DirectClusterResponseBoundary : Set where
  constructor direct-cluster-response-boundary
  field
    intermediateQuantitativeClusterMarginRequired : Bool
    intermediateQuantitativeClusterMarginRequiredIsFalse :
      intermediateQuantitativeClusterMarginRequired ≡ false
    clusterMarginLowerTheoremRequired : Bool
    clusterMarginLowerTheoremRequiredIsFalse :
      clusterMarginLowerTheoremRequired ≡ false
    analyticPaymentCanAccessFinalBalance : Bool
    analyticPaymentCanAccessFinalBalanceIsFalse :
      analyticPaymentCanAccessFinalBalance ≡ false
    directBudgetBelowClusterResponseIsSingleScalarLeaf : Bool
    directBudgetBelowClusterResponseIsSingleScalarLeafIsTrue :
      directBudgetBelowClusterResponseIsSingleScalarLeaf ≡ true
    paymentPlusDownstreamBalanceCompilesContradiction : Bool
    paymentPlusDownstreamBalanceCompilesContradictionIsTrue :
      paymentPlusDownstreamBalanceCompilesContradiction ≡ true
    paymentInhabitedHere : Bool
    paymentInhabitedHereIsFalse : paymentInhabitedHere ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    highestAlphaReading : String

canonicalDirectClusterResponseBoundary : DirectClusterResponseBoundary
canonicalDirectClusterResponseBoundary =
  direct-cluster-response-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "State the independent analytic theorem directly as complementBudget < literal ClusterResponse on a balance-free context. Existing Off/Gamma uppers compile complementResponse <= complementBudget; only afterward attach clusterResponse = complementResponse. This deletes the separate M_cluster <= ClusterResponse theorem without using the final balance to prove the analytic payment. The direct strict theorem remains unproved and RH is not derived."
