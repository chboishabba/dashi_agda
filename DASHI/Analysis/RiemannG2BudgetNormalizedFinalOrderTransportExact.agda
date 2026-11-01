module DASHI.Analysis.RiemannG2BudgetNormalizedFinalOrderTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as OffTransport
import DASHI.Analysis.RiemannG2BudgetNormalizedAnalyticCoresExact as Normalized
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
-- NORMALIZED CORES -> FINAL ORDER TRANSPORT WITH ACTUAL-BUDGET MARGIN
--
-- Once the channel allowances are definitionally chosen to be the actual
-- producer budgets, the final strict allowance theorem should not be restated
-- as an independent analytic payment.  This owner exposes the literal theorem
-- that remains:
--
--   cast(B_off) + cast(B_Gamma) < cast(M_cluster).
--
-- All other fields below are representation/order/same-object coordinates of
-- the existing final order-transport package.
------------------------------------------------------------------------

record BudgetNormalizedCorePair
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S) : Set₁ where
  field
    offInput : Normalized.BudgetNormalizedOffCoreInput S transport
    gammaInput : Normalized.BudgetNormalizedGammaCoreInput
    pairReference : String

open BudgetNormalizedCorePair public

compiledCores :
  forall {S transport} ->
  BudgetNormalizedCorePair S transport ->
  Core.FinalPoleQuotientTwoAnalyticCores
compiledCores pair =
  Core.final-pole-quotient-two-analytic-cores
    (Normalized.compileBudgetNormalizedOffCore (offInput pair))
    (Normalized.compileBudgetNormalizedGammaCore (gammaInput pair))
    (pairReference pair)

compiledPayments :
  forall {S transport}
    (pair : BudgetNormalizedCorePair S transport) ->
  Core.FinalPoleQuotientAnalyticCoreAttachments (compiledCores pair) ->
  Two.FinalPoleQuotientTwoPayments
compiledPayments pair attachments =
  Core.compileFinalTwoPayments (compiledCores pair) attachments

normalizedOffPaymentAllowanceIsActualBudget :
  forall {S transport}
    (pair : BudgetNormalizedCorePair S transport)
    (attachments : Core.FinalPoleQuotientAnalyticCoreAttachments (compiledCores pair)) ->
  let payments = compiledPayments pair attachments
      payment = Two.offPayment payments
      target = Payment.PoleQuotientOffAllowancePayment.target payment
  in Payment.PoleQuotientOffAllowancePayment.assignedOffAllowance payment
     ≡ Off.OffOrdinateBudget target (Off.universalPoleQuotientTaper target)
normalizedOffPaymentAllowanceIsActualBudget pair attachments = refl

normalizedGammaPaymentAllowanceIsActualBudget :
  forall {S transport}
    (pair : BudgetNormalizedCorePair S transport)
    (attachments : Core.FinalPoleQuotientAnalyticCoreAttachments (compiledCores pair)) ->
  let payments = compiledPayments pair attachments
      payment = Two.gammaPayment payments
      target = Payment.PoleQuotientGammaAllowancePayment.target payment
  in Payment.PoleQuotientGammaAllowancePayment.assignedGammaAllowance payment
     ≡ Gamma.GammaBudget target (Gamma.universalPoleQuotientTaper target)
normalizedGammaPaymentAllowanceIsActualBudget pair attachments = refl

record BudgetNormalizedFinalOrderTransportInput
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : OffTransport.ExplicitCutoffNearFarAgdaTransport S}
    (pair : BudgetNormalizedCorePair S transport)
    (attachments : Core.FinalPoleQuotientAnalyticCoreAttachments (compiledCores pair))
    : Set₁ where
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

    clusterEqualsOffPlusGamma :
      Existing.cast clusterScalarIdentity
        (Cluster.ClusterResponse cluster (Cluster.universalPoleQuotientTaper cluster))
      ≡ Split.add surface
          (Existing.cast offScalarIdentity
            (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off)))
          (Existing.cast gammaScalarIdentity
            (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma)))

    actualBudgetsStrictBelowMargin :
      Complement._<_ (Split.order surface)
        (Split.add surface
          (Existing.cast offScalarIdentity
            (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off)))
          (Existing.cast gammaScalarIdentity
            (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma))))
        (Existing.cast clusterScalarIdentity
          (Cluster.ClusterMargin cluster (Cluster.universalPoleQuotientTaper cluster)))

    transportReference : String

open BudgetNormalizedFinalOrderTransportInput public

compiledAllowanceMargin :
  forall {S transport pair attachments} ->
  (input : BudgetNormalizedFinalOrderTransportInput
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
  with normalizedOffPaymentAllowanceIsActualBudget pair attachments
     | normalizedGammaPaymentAllowanceIsActualBudget pair attachments
... | refl | refl = actualBudgetsStrictBelowMargin input

compileFinalOrderTransport :
  forall {S transport pair attachments} ->
  (input : BudgetNormalizedFinalOrderTransportInput
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
  BudgetNormalizedFinalOrderTransportInput
    {S = S} {transport = transport} pair attachments ->
  ⊥
compileHighOrdinateContradiction input =
  Final.orderTransportContradiction (compileFinalOrderTransport input)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record BudgetNormalizedFinalOrderTransportBoundary : Set where
  constructor budget-normalized-final-order-transport-boundary
  field
    separateOffAllowanceFitInFinalMarginRequired : Bool
    separateOffAllowanceFitInFinalMarginRequiredIsFalse :
      separateOffAllowanceFitInFinalMarginRequired ≡ false

    separateGammaAllowanceFitInFinalMarginRequired : Bool
    separateGammaAllowanceFitInFinalMarginRequiredIsFalse :
      separateGammaAllowanceFitInFinalMarginRequired ≡ false

    actualBudgetSumStrictMarginIsLiteralFinalScalarTheorem : Bool
    actualBudgetSumStrictMarginIsLiteralFinalScalarTheoremIsTrue :
      actualBudgetSumStrictMarginIsLiteralFinalScalarTheorem ≡ true

    sameObjectOrderTransportStillRequired : Bool
    sameObjectOrderTransportStillRequiredIsTrue :
      sameObjectOrderTransportStillRequired ≡ true

    normalizedFinalTransportCompilesExistingContradiction : Bool
    normalizedFinalTransportCompilesExistingContradictionIsTrue :
      normalizedFinalTransportCompilesExistingContradiction ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalBudgetNormalizedFinalOrderTransportBoundary :
  BudgetNormalizedFinalOrderTransportBoundary
canonicalBudgetNormalizedFinalOrderTransportBoundary =
  budget-normalized-final-order-transport-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "With channel allowances normalized to the actual producer budgets, the final scalar compatibility theorem is literally cast(B_off)+cast(B_Gamma)<cast(M_cluster). The two allowance-fit inequalities disappear from the final margin API. Scalar/order/taper identity, cluster=off+Gamma and the cluster target remain explicit representation inputs. These data compile the existing FinalPoleQuotientOrderTransport and its contradiction without changing the final consumer. No RH theorem is fabricated here."
