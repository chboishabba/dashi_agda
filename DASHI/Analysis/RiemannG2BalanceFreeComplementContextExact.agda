module DASHI.Analysis.RiemannG2BalanceFreeComplementContextExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2DirectComplementUnpaidContextExact as Unpaid
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Legacy
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing

------------------------------------------------------------------------
-- BALANCE-FREE ANALYTIC CONTEXT
--
-- The previous unpaid context removed the strict margin from its own indices,
-- but it still exposed the terminal balance
--
--   cluster = Off + Gamma.
--
-- Therefore a term inhabiting the strict-margin payment could still depend on
-- that final balance despite carrying a prose-style independence receipt.
-- Dependency independence is stronger when the forbidden theorem is absent from
-- the analytic context entirely.
--
-- This record contains every representation/order/taper/cluster coordinate
-- needed to STATE the margin, but deliberately no cluster-balance equality.
------------------------------------------------------------------------

record BalanceFreeComplementContext
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    (targets : Direct.DirectLiteralComplementTargets S transport) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
  field
    surface : Split.OrderedAdditiveComplementSurface
    cluster : Cluster.PoleQuotientClusterMarginTarget

    offScalarIdentity :
      Off.Scalar off ≡ Complement.Scalar (Split.order surface)
    gammaScalarIdentity :
      Gamma.Scalar gamma ≡ Complement.Scalar (Split.order surface)
    clusterScalarIdentity :
      Cluster.Scalar cluster ≡ Complement.Scalar (Split.order surface)

    offGammaTaperCarrierIdentity : Off.Taper off ≡ Gamma.Taper gamma
    offClusterTaperCarrierIdentity : Off.Taper off ≡ Cluster.Taper cluster

    sameUniversalTaperOffGamma :
      Existing.cast offGammaTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Gamma.universalPoleQuotientTaper gamma

    sameUniversalTaperOffCluster :
      Existing.cast offClusterTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Cluster.universalPoleQuotientTaper cluster

    offOrderTransport :
      {x y : Off.Scalar off} ->
      Off._≤_ off x y ->
      Complement._≤_ (Split.order surface)
        (Existing.cast offScalarIdentity x)
        (Existing.cast offScalarIdentity y)

    gammaOrderTransport :
      {x y : Gamma.Scalar gamma} ->
      Gamma._≤_ gamma x y ->
      Complement._≤_ (Split.order surface)
        (Existing.cast gammaScalarIdentity x)
        (Existing.cast gammaScalarIdentity y)

    clusterOrderTransport :
      {x y : Cluster.Scalar cluster} ->
      Cluster._≤_ cluster x y ->
      Complement._≤_ (Split.order surface)
        (Existing.cast clusterScalarIdentity x)
        (Existing.cast clusterScalarIdentity y)

    contextReference : String

open BalanceFreeComplementContext public

------------------------------------------------------------------------
-- The final balance is a downstream attachment, not an analytic input.
------------------------------------------------------------------------

record FinalClusterBalanceAttachment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : BalanceFreeComplementContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
    cluster0 = cluster context
  field
    clusterEqualsOffPlusGamma :
      Existing.cast (clusterScalarIdentity context)
        (Cluster.ClusterResponse cluster0
          (Cluster.universalPoleQuotientTaper cluster0))
      ≡ Split.add (surface context)
          (Existing.cast (offScalarIdentity context)
            (Off.OffOrdinateResponse off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast (gammaScalarIdentity context)
            (Gamma.GammaResponse gamma
              (Gamma.universalPoleQuotientTaper gamma)))

    balanceReference : String

open FinalClusterBalanceAttachment public

------------------------------------------------------------------------
-- Strict analytic payment on the balance-free context.
------------------------------------------------------------------------

record BalanceFreeJointMarginPayment
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    {targets : Direct.DirectLiteralComplementTargets S transport}
    (context : BalanceFreeComplementContext targets) : Set₁ where
  private
    off = Direct.directOffTarget targets
    gamma = Direct.directGammaTarget targets
    cluster0 = cluster context
  field
    strictMargin :
      Complement._<_ (Split.order (surface context))
        (Split.add (surface context)
          (Existing.cast (offScalarIdentity context)
            (Off.OffOrdinateBudget off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast (gammaScalarIdentity context)
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast (clusterScalarIdentity context)
          (Cluster.ClusterMargin cluster0
            (Cluster.universalPoleQuotientTaper cluster0)))

    paymentReference : String

open BalanceFreeJointMarginPayment public

------------------------------------------------------------------------
-- Downstream compatibility: only after the payment exists do we reattach the
-- final balance and recover the older combined final input.
------------------------------------------------------------------------

compileBalanceFreeToPreviousUnpaidContext :
  forall {S transport targets} ->
  (context : BalanceFreeComplementContext
    {S = S} {transport = transport} targets) ->
  FinalClusterBalanceAttachment context ->
  Unpaid.DirectComplementUnpaidContext targets
compileBalanceFreeToPreviousUnpaidContext context balance = record
  { Unpaid.surface = surface context
  ; Unpaid.cluster = cluster context
  ; Unpaid.offScalarIdentity = offScalarIdentity context
  ; Unpaid.gammaScalarIdentity = gammaScalarIdentity context
  ; Unpaid.clusterScalarIdentity = clusterScalarIdentity context
  ; Unpaid.offGammaTaperCarrierIdentity = offGammaTaperCarrierIdentity context
  ; Unpaid.offClusterTaperCarrierIdentity = offClusterTaperCarrierIdentity context
  ; Unpaid.sameUniversalTaperOffGamma = sameUniversalTaperOffGamma context
  ; Unpaid.sameUniversalTaperOffCluster = sameUniversalTaperOffCluster context
  ; Unpaid.offOrderTransport = offOrderTransport context
  ; Unpaid.gammaOrderTransport = gammaOrderTransport context
  ; Unpaid.clusterOrderTransport = clusterOrderTransport context
  ; Unpaid.clusterEqualsOffPlusGamma = clusterEqualsOffPlusGamma balance
  ; Unpaid.complementEstimateIndependentOfFinalBalance = ⊤
  ; Unpaid.complementEstimateIndependentOfFinalBalanceReceipt = tt
  ; Unpaid.contextReference = contextReference context
  }

compileBalanceFreePaymentToPreviousPayment :
  forall {S transport targets}
    {context : BalanceFreeComplementContext
      {S = S} {transport = transport} targets} ->
  (balance : FinalClusterBalanceAttachment context) ->
  BalanceFreeJointMarginPayment context ->
  Unpaid.CanonicalJointMarginPayment
    (compileBalanceFreeToPreviousUnpaidContext context balance)
compileBalanceFreePaymentToPreviousPayment balance payment = record
  { Unpaid.literalComplementStrictBelowMargin = strictMargin payment
  ; Unpaid.paymentReference = paymentReference payment
  }

compileBalanceFreePaymentToLegacyInput :
  forall {S transport targets}
    {context : BalanceFreeComplementContext
      {S = S} {transport = transport} targets} ->
  (balance : FinalClusterBalanceAttachment context) ->
  BalanceFreeJointMarginPayment context ->
  Legacy.DirectIndependentComplementMarginInput targets
compileBalanceFreePaymentToLegacyInput {context = context} balance payment =
  Unpaid.compileContextAndPaymentToLegacyInput
    (compileBalanceFreeToPreviousUnpaidContext context balance)
    (compileBalanceFreePaymentToPreviousPayment balance payment)

balanceFreePaymentContradiction :
  forall {S transport targets}
    {context : BalanceFreeComplementContext
      {S = S} {transport = transport} targets} ->
  FinalClusterBalanceAttachment context ->
  BalanceFreeJointMarginPayment context ->
  ⊥
balanceFreePaymentContradiction balance payment =
  Legacy.directIndependentComplementContradiction
    (compileBalanceFreePaymentToLegacyInput balance payment)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record BalanceFreeContextBoundary : Set where
  constructor balance-free-context-boundary
  field
    analyticContextExposesFinalClusterBalance : Bool
    analyticContextExposesFinalClusterBalanceIsFalse :
      analyticContextExposesFinalClusterBalance ≡ false

    finalBalanceIsDownstreamAttachment : Bool
    finalBalanceIsDownstreamAttachmentIsTrue :
      finalBalanceIsDownstreamAttachment ≡ true

    strictMarginPaymentCanBeTypedWithoutFinalBalance : Bool
    strictMarginPaymentCanBeTypedWithoutFinalBalanceIsTrue :
      strictMarginPaymentCanBeTypedWithoutFinalBalance ≡ true

    oldFinalConsumerRecoverableAfterBalanceAttachment : Bool
    oldFinalConsumerRecoverableAfterBalanceAttachmentIsTrue :
      oldFinalConsumerRecoverableAfterBalanceAttachment ≡ true

    splittingBalanceFromAnalyticContextProvesMargin : Bool
    splittingBalanceFromAnalyticContextProvesMarginIsFalse :
      splittingBalanceFromAnalyticContextProvesMargin ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalBalanceFreeContextBoundary : BalanceFreeContextBoundary
canonicalBalanceFreeContextBoundary =
  balance-free-context-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The analytic payment is now dependency-level independent of the final balance: BalanceFreeComplementContext does not contain cluster=Off+Gamma at all. The strict margin is typed on that context alone. Only after the payment exists is FinalClusterBalanceAttachment supplied to recover the historical final consumer and contradiction. This is stronger than an opaque independence receipt because the forbidden theorem is absent from the analytic input type. The split does not prove the margin or RH."
