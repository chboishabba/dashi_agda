module DASHI.Analysis.RiemannG2IndependentComplementMarginFinalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2LiteralResponseNormalizedAnalyticCoresExact as Literal
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannG2FinalPoleQuotientTwoPaymentCutExact as Two
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as Final

------------------------------------------------------------------------
-- ONE-LEAF FINAL ANALYTIC ROUTE
--
-- With literal-response normalization, the channel core budgets are
--
--   Off:   D_near(J) + B_far(J)
--   Gamma: D_Gamma(g_pole).
--
-- Their source-order upper/allowance fields are reflexivity.  The one remaining
-- quantitative theorem is therefore the literal strict complement margin after
-- same-scalar transport.  It must be proved independently of the final balance
-- identity; that identity is retained below as a separate representation field.
------------------------------------------------------------------------

compiledPayments :
  forall {S transport}
    (pair : Literal.LiteralResponseNormalizedCorePair S transport) ->
  Core.FinalPoleQuotientAnalyticCoreAttachments
    (Literal.compiledLiteralCores pair) ->
  Two.FinalPoleQuotientTwoPayments
compiledPayments pair attachments =
  Core.compileFinalTwoPayments
    (Literal.compiledLiteralCores pair)
    attachments

literalOffPaymentAllowanceIsBudget :
  forall {S transport}
    (pair : Literal.LiteralResponseNormalizedCorePair S transport)
    (attachments : Core.FinalPoleQuotientAnalyticCoreAttachments
      (Literal.compiledLiteralCores pair)) ->
  let payments = compiledPayments pair attachments
      payment = Two.offPayment payments
      target = Payment.PoleQuotientOffAllowancePayment.target payment
  in Payment.PoleQuotientOffAllowancePayment.assignedOffAllowance payment
     ≡ Off.OffOrdinateBudget target (Off.universalPoleQuotientTaper target)
literalOffPaymentAllowanceIsBudget pair attachments = refl

literalGammaPaymentAllowanceIsBudget :
  forall {S transport}
    (pair : Literal.LiteralResponseNormalizedCorePair S transport)
    (attachments : Core.FinalPoleQuotientAnalyticCoreAttachments
      (Literal.compiledLiteralCores pair)) ->
  let payments = compiledPayments pair attachments
      payment = Two.gammaPayment payments
      target = Payment.PoleQuotientGammaAllowancePayment.target payment
  in Payment.PoleQuotientGammaAllowancePayment.assignedGammaAllowance payment
     ≡ Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target)
literalGammaPaymentAllowanceIsBudget pair attachments = refl

record IndependentComplementMarginFinalInput
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    (pair : Literal.LiteralResponseNormalizedCorePair S transport)
    (attachments : Core.FinalPoleQuotientAnalyticCoreAttachments
      (Literal.compiledLiteralCores pair)) : Set₁ where
  private
    payments = compiledPayments pair attachments
    offPayment = Two.offPayment payments
    gammaPayment = Two.gammaPayment payments
    off = Payment.PoleQuotientOffAllowancePayment.target offPayment
    gamma = Payment.PoleQuotientGammaAllowancePayment.target gammaPayment
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

    -- Representation theorem used only after the independent margin exists.
    clusterEqualsOffPlusGamma :
      Existing.cast clusterScalarIdentity
        (Cluster.ClusterResponse cluster
          (Cluster.universalPoleQuotientTaper cluster))
      ≡ Split.add surface
          (Existing.cast offScalarIdentity
            (Off.OffOrdinateResponse off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast gammaScalarIdentity
            (Gamma.GammaResponse gamma
              (Gamma.universalPoleQuotientTaper gamma)))

    complementEstimateIndependentOfFinalBalance : Set
    complementEstimateIndependentOfFinalBalanceReceipt :
      complementEstimateIndependentOfFinalBalance

    literalComplementStrictBelowMargin :
      Complement._<_ (Split.order surface)
        (Split.add surface
          (Existing.cast offScalarIdentity
            (Off.OffOrdinateBudget off
              (Off.universalPoleQuotientTaper off)))
          (Existing.cast gammaScalarIdentity
            (Gamma.GammaBudget gamma
              (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast clusterScalarIdentity
          (Cluster.ClusterMargin cluster
            (Cluster.universalPoleQuotientTaper cluster)))

    estimateReference : String
    transportReference : String

open IndependentComplementMarginFinalInput public

compiledAllowanceMargin :
  forall {S transport pair attachments} ->
  (input : IndependentComplementMarginFinalInput
    {S = S} {transport = transport} pair attachments) ->
  let payments = compiledPayments pair attachments
      offPayment = Two.offPayment payments
      gammaPayment = Two.gammaPayment payments
      off = Payment.PoleQuotientOffAllowancePayment.target offPayment
      gamma = Payment.PoleQuotientGammaAllowancePayment.target gammaPayment
  in Complement._<_ (Split.order (surface input))
      (Split.add (surface input)
        (Existing.cast (offScalarIdentity input)
          (Payment.PoleQuotientOffAllowancePayment.assignedOffAllowance offPayment))
        (Existing.cast (gammaScalarIdentity input)
          (Payment.PoleQuotientGammaAllowancePayment.assignedGammaAllowance gammaPayment)))
      (Existing.cast (clusterScalarIdentity input)
        (Cluster.ClusterMargin (cluster input)
          (Cluster.universalPoleQuotientTaper (cluster input))))
compiledAllowanceMargin {pair = pair} {attachments = attachments} input
  with literalOffPaymentAllowanceIsBudget pair attachments
     | literalGammaPaymentAllowanceIsBudget pair attachments
... | refl | refl = literalComplementStrictBelowMargin input

compileFinalOrderTransport :
  forall {S transport pair attachments} ->
  (input : IndependentComplementMarginFinalInput
    {S = S} {transport = transport} pair attachments) ->
  let payments = compiledPayments pair attachments
  in Final.FinalPoleQuotientOrderTransport
      (surface input)
      (Two.offPayment payments)
      (Two.gammaPayment payments)
      (cluster input)
compileFinalOrderTransport input = record
  { Final.offScalarIdentity = offScalarIdentity input
  ; Final.gammaScalarIdentity = gammaScalarIdentity input
  ; Final.clusterScalarIdentity = clusterScalarIdentity input
  ; Final.offGammaTaperCarrierIdentity = offGammaTaperCarrierIdentity input
  ; Final.offClusterTaperCarrierIdentity = offClusterTaperCarrierIdentity input
  ; Final.sameUniversalTaperOffGamma = sameUniversalTaperOffGamma input
  ; Final.sameUniversalTaperOffCluster = sameUniversalTaperOffCluster input
  ; Final.offOrderTransport = offOrderTransport input
  ; Final.gammaOrderTransport = gammaOrderTransport input
  ; Final.clusterOrderTransport = clusterOrderTransport input
  ; Final.clusterEqualsOffPlusGamma = clusterEqualsOffPlusGamma input
  ; Final.allowancesStrictBelowMargin = compiledAllowanceMargin input
  ; Final.transportReference = transportReference input
  }

compileHighOrdinateContradiction :
  forall {S transport pair attachments} ->
  IndependentComplementMarginFinalInput
    {S = S} {transport = transport} pair attachments ->
  ⊥
compileHighOrdinateContradiction input =
  Final.orderTransportContradiction (compileFinalOrderTransport input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record IndependentComplementMarginBoundary : Set where
  constructor independent-complement-margin-boundary
  field
    separateFiniteNearUpperLeafRequired : Bool
    separateFiniteNearUpperLeafRequiredIsFalse :
      separateFiniteNearUpperLeafRequired ≡ false

    separateGammaUpperLeafRequired : Bool
    separateGammaUpperLeafRequiredIsFalse :
      separateGammaUpperLeafRequired ≡ false

    transportedFarShellBoundStillUsed : Bool
    transportedFarShellBoundStillUsedIsTrue :
      transportedFarShellBoundStillUsed ≡ true

    oneIndependentComplementMarginIsScalarLeaf : Bool
    oneIndependentComplementMarginIsScalarLeafIsTrue :
      oneIndependentComplementMarginIsScalarLeaf ≡ true

    finalBalanceMayBeUsedToProveThatMargin : Bool
    finalBalanceMayBeUsedToProveThatMarginIsFalse :
      finalBalanceMayBeUsedToProveThatMargin ≡ false

    representationAndOrderTransportRemainSeparate : Bool
    representationAndOrderTransportRemainSeparateIsTrue :
      representationAndOrderTransportRemainSeparate ≡ true

    oneLeafCompilesExistingContradiction : Bool
    oneLeafCompilesExistingContradictionIsTrue :
      oneLeafCompilesExistingContradiction ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalIndependentComplementMarginBoundary :
  IndependentComplementMarginBoundary
canonicalIndependentComplementMarginBoundary =
  independent-complement-margin-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    "After literal-response normalization, the scalar terminal cut is one theorem: independently prove the same-case surviving complement D_near(J)+B_far(J)+D_Gamma lies strictly below the quantitative cluster margin. The checked far-shell upper remains genuine input. Near and Gamma standalone upper envelopes are no longer primitive leaves because their budgets may be their literal responses under source-order reflexivity. The final cluster=Off+Gamma balance is a later representation theorem and may not manufacture the margin. With the usual scalar/order/taper attachments, this one scalar leaf compiles the existing high-ordinate contradiction. RH is not derived here."
