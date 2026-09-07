module DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannG2FinalSplitComplementAllowanceAssemblyExact as Assembly
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster

------------------------------------------------------------------------
-- SAME-ORDER TRANSPORT COMPILER
--
-- Final allowance assembly previously required four transported inequalities as
-- independent fields. But each analytic target/payment already proves those
-- inequalities in its own scalar order. The actual representation obligation is
-- stronger and smaller: transport each source order relation to the final order
-- once. Then the channel upper bounds and allowance fits are compiler output.
------------------------------------------------------------------------

record FinalPoleQuotientOrderTransport
    (surface : Split.OrderedAdditiveComplementSurface)
    (offPayment : Payment.PoleQuotientOffAllowancePayment)
    (gammaPayment : Payment.PoleQuotientGammaAllowancePayment)
    (cluster : Cluster.PoleQuotientClusterMarginTarget) : Set₁ where
  private
    off = Payment.PoleQuotientOffAllowancePayment.target offPayment
    gamma = Payment.PoleQuotientGammaAllowancePayment.target gammaPayment
    FinalScalar = Complement.Scalar (Split.order surface)

  field
    offScalarIdentity : Off.Scalar off ≡ FinalScalar
    gammaScalarIdentity : Gamma.Scalar gamma ≡ FinalScalar
    clusterScalarIdentity : Cluster.Scalar cluster ≡ FinalScalar

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
      {x y : Off.Scalar off} →
      Off._≤_ off x y →
      Complement._≤_ (Split.order surface)
        (Existing.cast offScalarIdentity x)
        (Existing.cast offScalarIdentity y)

    gammaOrderTransport :
      {x y : Gamma.Scalar gamma} →
      Gamma._≤_ gamma x y →
      Complement._≤_ (Split.order surface)
        (Existing.cast gammaScalarIdentity x)
        (Existing.cast gammaScalarIdentity y)

    clusterOrderTransport :
      {x y : Cluster.Scalar cluster} →
      Cluster._≤_ cluster x y →
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

    allowancesStrictBelowMargin :
      Complement._<_ (Split.order surface)
        (Split.add surface
          (Existing.cast offScalarIdentity (Payment.assignedOffAllowance offPayment))
          (Existing.cast gammaScalarIdentity (Payment.assignedGammaAllowance gammaPayment)))
        (Existing.cast clusterScalarIdentity
          (Cluster.ClusterMargin cluster (Cluster.universalPoleQuotientTaper cluster)))

    transportReference : String

open FinalPoleQuotientOrderTransport public

compiledOffUpper :
  ∀ {surface offPayment gammaPayment cluster} →
  (t : FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster) →
  let off = Payment.PoleQuotientOffAllowancePayment.target offPayment
  in Complement._≤_ (Split.order surface)
      (Existing.cast (offScalarIdentity t)
        (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off)))
      (Existing.cast (offScalarIdentity t)
        (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off)))
compiledOffUpper {offPayment = offPayment} t =
  offOrderTransport t
    (Off.signedOffOrdinateUpper
      (Payment.PoleQuotientOffAllowancePayment.target offPayment))

compiledGammaUpper :
  ∀ {surface offPayment gammaPayment cluster} →
  (t : FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster) →
  let gamma = Payment.PoleQuotientGammaAllowancePayment.target gammaPayment
  in Complement._≤_ (Split.order surface)
      (Existing.cast (gammaScalarIdentity t)
        (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma)))
      (Existing.cast (gammaScalarIdentity t)
        (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma)))
compiledGammaUpper {gammaPayment = gammaPayment} t =
  gammaOrderTransport t
    (Gamma.gammaResponseUpper
      (Payment.PoleQuotientGammaAllowancePayment.target gammaPayment))

compiledClusterLower :
  ∀ {surface offPayment gammaPayment cluster} →
  (t : FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster) →
  Complement._≤_ (Split.order surface)
    (Existing.cast (clusterScalarIdentity t)
      (Cluster.ClusterMargin cluster (Cluster.universalPoleQuotientTaper cluster)))
    (Existing.cast (clusterScalarIdentity t)
      (Cluster.ClusterResponse cluster (Cluster.universalPoleQuotientTaper cluster)))
compiledClusterLower {cluster = cluster} t =
  clusterOrderTransport t (Cluster.quantitativeClusterMarginLower cluster)

compiledOffAllowanceFit :
  ∀ {surface offPayment gammaPayment cluster} →
  (t : FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster) →
  let off = Payment.PoleQuotientOffAllowancePayment.target offPayment
  in Complement._≤_ (Split.order surface)
      (Existing.cast (offScalarIdentity t)
        (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off)))
      (Existing.cast (offScalarIdentity t)
        (Payment.assignedOffAllowance offPayment))
compiledOffAllowanceFit {offPayment = offPayment} t =
  offOrderTransport t (Payment.offBudgetBelowAssignedAllowance offPayment)

compiledGammaAllowanceFit :
  ∀ {surface offPayment gammaPayment cluster} →
  (t : FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster) →
  let gamma = Payment.PoleQuotientGammaAllowancePayment.target gammaPayment
  in Complement._≤_ (Split.order surface)
      (Existing.cast (gammaScalarIdentity t)
        (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma)))
      (Existing.cast (gammaScalarIdentity t)
        (Payment.assignedGammaAllowance gammaPayment))
compiledGammaAllowanceFit {gammaPayment = gammaPayment} t =
  gammaOrderTransport t (Payment.gammaBudgetBelowAssignedAllowance gammaPayment)

compileFinalAllowanceAssembly :
  ∀ {surface offPayment gammaPayment cluster} →
  FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster →
  Assembly.FinalSplitComplementAllowanceAssembly
    surface offPayment gammaPayment cluster
compileFinalAllowanceAssembly
    {surface} {offPayment} {gammaPayment} {cluster} t = record
  { Assembly.offScalarIdentity = offScalarIdentity t
  ; Assembly.gammaScalarIdentity = gammaScalarIdentity t
  ; Assembly.clusterScalarIdentity = clusterScalarIdentity t
  ; Assembly.offGammaTaperCarrierIdentity = offGammaTaperCarrierIdentity t
  ; Assembly.offClusterTaperCarrierIdentity = offClusterTaperCarrierIdentity t
  ; Assembly.sameUniversalTaperOffGamma = sameUniversalTaperOffGamma t
  ; Assembly.sameUniversalTaperOffCluster = sameUniversalTaperOffCluster t
  ; Assembly.offOrdinateResponse =
      Existing.cast (offScalarIdentity t)
        (Off.OffOrdinateResponse
          (Payment.PoleQuotientOffAllowancePayment.target offPayment)
          (Off.universalPoleQuotientTaper
            (Payment.PoleQuotientOffAllowancePayment.target offPayment)))
  ; Assembly.offOrdinateResponseIsProducer = refl
  ; Assembly.offOrdinateBudget =
      Existing.cast (offScalarIdentity t)
        (Off.OffOrdinateBudget
          (Payment.PoleQuotientOffAllowancePayment.target offPayment)
          (Off.universalPoleQuotientTaper
            (Payment.PoleQuotientOffAllowancePayment.target offPayment)))
  ; Assembly.offOrdinateBudgetIsProducer = refl
  ; Assembly.gammaResidual =
      Existing.cast (gammaScalarIdentity t)
        (Gamma.GammaResponse
          (Payment.PoleQuotientGammaAllowancePayment.target gammaPayment)
          (Gamma.universalPoleQuotientTaper
            (Payment.PoleQuotientGammaAllowancePayment.target gammaPayment)))
  ; Assembly.gammaResidualIsProducer = refl
  ; Assembly.gammaBudget =
      Existing.cast (gammaScalarIdentity t)
        (Gamma.GammaBudget
          (Payment.PoleQuotientGammaAllowancePayment.target gammaPayment)
          (Gamma.universalPoleQuotientTaper
            (Payment.PoleQuotientGammaAllowancePayment.target gammaPayment)))
  ; Assembly.gammaBudgetIsProducer = refl
  ; Assembly.clusterResponse =
      Existing.cast (clusterScalarIdentity t)
        (Cluster.ClusterResponse cluster (Cluster.universalPoleQuotientTaper cluster))
  ; Assembly.clusterResponseIsProducer = refl
  ; Assembly.clusterMargin =
      Existing.cast (clusterScalarIdentity t)
        (Cluster.ClusterMargin cluster (Cluster.universalPoleQuotientTaper cluster))
  ; Assembly.clusterMarginIsProducer = refl
  ; Assembly.clusterEqualsOffPlusGamma = clusterEqualsOffPlusGamma t
  ; Assembly.clusterMarginLower = compiledClusterLower t
  ; Assembly.offOrdinateUpper = compiledOffUpper t
  ; Assembly.gammaUpper = compiledGammaUpper t
  ; Assembly.offAllowance =
      Existing.cast (offScalarIdentity t) (Payment.assignedOffAllowance offPayment)
  ; Assembly.offAllowanceIsProducerAssignment = refl
  ; Assembly.gammaAllowance =
      Existing.cast (gammaScalarIdentity t) (Payment.assignedGammaAllowance gammaPayment)
  ; Assembly.gammaAllowanceIsProducerAssignment = refl
  ; Assembly.offBudgetBelowAssignedAllowance = compiledOffAllowanceFit t
  ; Assembly.gammaBudgetBelowAssignedAllowance = compiledGammaAllowanceFit t
  ; Assembly.allowancesStrictBelowMargin = allowancesStrictBelowMargin t
  ; Assembly.assemblyReference = transportReference t
  }

orderTransportContradiction :
  ∀ {surface offPayment gammaPayment cluster} →
  FinalPoleQuotientOrderTransport surface offPayment gammaPayment cluster →
  ⊥
orderTransportContradiction {surface} t =
  Assembly.assemblyContradiction {surface = surface}
    (compileFinalAllowanceAssembly t)

record FinalOrderTransportBoundary : Set where
  constructor final-order-transport-boundary
  field
    fourChannelInequalitiesNeedIndependentFinalProofs : Bool
    fourChannelInequalitiesNeedIndependentFinalProofsIsFalse :
      fourChannelInequalitiesNeedIndependentFinalProofs ≡ false

    sourceOrdersStillNeedTransportToFinalOrder : Bool
    sourceOrdersStillNeedTransportToFinalOrderIsTrue :
      sourceOrdersStillNeedTransportToFinalOrder ≡ true

    finalClusterBalanceStillSameObjectReceipt : Bool
    finalClusterBalanceStillSameObjectReceiptIsTrue :
      finalClusterBalanceStillSameObjectReceipt ≡ true

    strictAllowanceSumStillFinalConsumerReceipt : Bool
    strictAllowanceSumStillFinalConsumerReceiptIsTrue :
      strictAllowanceSumStillFinalConsumerReceipt ≡ true

    orderTransportPackageCompilesContradiction : Bool
    orderTransportPackageCompilesContradictionIsTrue :
      orderTransportPackageCompilesContradiction ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalOrderTransportBoundary : FinalOrderTransportBoundary
canonicalFinalOrderTransportBoundary =
  final-order-transport-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    "Transport each Off/Gamma/Cluster source order relation to the final ordered scalar once. Then the existing target upper/lower theorems and the analytic assigned-allowance fits transport automatically; do not re-prove those four inequalities independently after scalar identification. The genuinely cross-channel downstream receipts are only same universal taper/carrier identity, the final cluster = off + Gamma balance, and A_off + A_Gamma < M_cluster. From those, the existing allowance assembly and contradiction are compiler output. RH is not derived without the literal analytic payments."
