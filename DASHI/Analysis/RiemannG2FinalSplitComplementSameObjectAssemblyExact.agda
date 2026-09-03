module DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster

------------------------------------------------------------------------
-- FINAL SAME-OBJECT INPUT ASSEMBLY
--
-- The final contradiction compiler already consumes one ordered scalar carrier.
-- The three analytic producer APIs (off, Gamma, cluster) each carry their own
-- abstract Scalar/Taper types.  Cardinality/name agreement is not enough: the
-- literal producer values must be transported into the SAME final scalar and
-- the universal pole-quotient taper must be the SAME taper across all channels.
------------------------------------------------------------------------

cast : ∀ {A B : Set} → A ≡ B → A → B
cast refl x = x

record FinalSplitComplementProducerAssembly
    (surface : Split.OrderedAdditiveComplementSurface)
    (off : Off.PoleQuotientOffOrdinateBudgetTarget)
    (gamma : Gamma.PoleQuotientGammaBudgetTarget)
    (cluster : Cluster.PoleQuotientClusterMarginTarget) : Set₁ where
  private
    FinalScalar = Complement.Scalar (Split.order surface)

  field
    offScalarIdentity : Off.Scalar off ≡ FinalScalar
    gammaScalarIdentity : Gamma.Scalar gamma ≡ FinalScalar
    clusterScalarIdentity : Cluster.Scalar cluster ≡ FinalScalar

    offGammaTaperCarrierIdentity : Off.Taper off ≡ Gamma.Taper gamma
    offClusterTaperCarrierIdentity : Off.Taper off ≡ Cluster.Taper cluster

    sameUniversalTaperOffGamma :
      cast offGammaTaperCarrierIdentity (Off.universalPoleQuotientTaper off)
      ≡ Gamma.universalPoleQuotientTaper gamma

    sameUniversalTaperOffCluster :
      cast offClusterTaperCarrierIdentity (Off.universalPoleQuotientTaper off)
      ≡ Cluster.universalPoleQuotientTaper cluster

    -- Final-carrier values are literal transports of the producer values.
    offOrdinateResponse : FinalScalar
    offOrdinateResponseIsProducer :
      offOrdinateResponse
      ≡ cast offScalarIdentity
          (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off))

    offOrdinateBudget : FinalScalar
    offOrdinateBudgetIsProducer :
      offOrdinateBudget
      ≡ cast offScalarIdentity
          (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off))

    gammaResidual : FinalScalar
    gammaResidualIsProducer :
      gammaResidual
      ≡ cast gammaScalarIdentity
          (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma))

    gammaBudget : FinalScalar
    gammaBudgetIsProducer :
      gammaBudget
      ≡ cast gammaScalarIdentity
          (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma))

    clusterResponse : FinalScalar
    clusterResponseIsProducer :
      clusterResponse
      ≡ cast clusterScalarIdentity
          (Cluster.ClusterResponse cluster (Cluster.universalPoleQuotientTaper cluster))

    clusterMargin : FinalScalar
    clusterMarginIsProducer :
      clusterMargin
      ≡ cast clusterScalarIdentity
          (Cluster.ClusterMargin cluster (Cluster.universalPoleQuotientTaper cluster))

    -- These are exactly the final consumer receipts, now on one scalar/order.
    clusterEqualsOffPlusGamma :
      clusterResponse ≡ Split.add surface offOrdinateResponse gammaResidual

    clusterMarginLower :
      Complement._≤_ (Split.order surface) clusterMargin clusterResponse

    offOrdinateUpper :
      Complement._≤_ (Split.order surface) offOrdinateResponse offOrdinateBudget

    gammaUpper :
      Complement._≤_ (Split.order surface) gammaResidual gammaBudget

    splitBudgetStrictBelowMargin :
      Complement._<_ (Split.order surface)
        (Split.add surface offOrdinateBudget gammaBudget)
        clusterMargin

    assemblyReference : String

open FinalSplitComplementProducerAssembly public

------------------------------------------------------------------------
-- Compiler: once the same-object producer assembly is present, the existing
-- split-complement contradiction input is generated directly.
------------------------------------------------------------------------

assemblyToSplitComplementMargin :
  ∀ {surface off gamma cluster} →
  FinalSplitComplementProducerAssembly surface off gamma cluster →
  Split.SplitPoleQuotientComplementMargin surface
assemblyToSplitComplementMargin assembly =
  Split.split-pole-quotient-complement-margin
    (clusterResponse assembly)
    (offOrdinateResponse assembly)
    (gammaResidual assembly)
    (offOrdinateBudget assembly)
    (gammaBudget assembly)
    (clusterMargin assembly)
    (clusterEqualsOffPlusGamma assembly)
    (clusterMarginLower assembly)
    (offOrdinateUpper assembly)
    (gammaUpper assembly)
    (splitBudgetStrictBelowMargin assembly)

assemblyContradiction :
  ∀ {surface off gamma cluster} →
  FinalSplitComplementProducerAssembly surface off gamma cluster →
  ⊥
assemblyContradiction {surface} assembly =
  Split.splitPoleQuotientComplementContradiction
    surface
    (assemblyToSplitComplementMargin assembly)

------------------------------------------------------------------------
-- Search consequences.
------------------------------------------------------------------------

data FinalAssemblyPayment : Set where
  rebuildFinalContradictionCompiler
  separatelyInventWholeComplementBudget
  attachOffProducerToFinalScalar
  attachGammaProducerToFinalScalar
  attachClusterProducerToFinalScalar
  proveSameUniversalTaper
  proveFinalClusterBalance
  proveFinalThreeChannelBounds
  proveStrictCombinedBudget
  : FinalAssemblyPayment

data PaymentStatus : Set where
  pruned live downstream : PaymentStatus

paymentStatus : FinalAssemblyPayment → PaymentStatus
paymentStatus rebuildFinalContradictionCompiler = pruned
paymentStatus separatelyInventWholeComplementBudget = pruned
paymentStatus attachOffProducerToFinalScalar = live
paymentStatus attachGammaProducerToFinalScalar = live
paymentStatus attachClusterProducerToFinalScalar = live
paymentStatus proveSameUniversalTaper = live
paymentStatus proveFinalClusterBalance = live
paymentStatus proveFinalThreeChannelBounds = live
paymentStatus proveStrictCombinedBudget = live

finalCompilerRebuildPruned :
  paymentStatus rebuildFinalContradictionCompiler ≡ pruned
finalCompilerRebuildPruned = refl

wholeComplementBudgetInventionPruned :
  paymentStatus separatelyInventWholeComplementBudget ≡ pruned
wholeComplementBudgetInventionPruned = refl

record FinalSplitSameObjectBoundary : Set where
  constructor final-split-same-object-boundary
  field
    finalCompilerAlreadyOwned : Bool
    finalCompilerAlreadyOwnedIsTrue : finalCompilerAlreadyOwned ≡ true

    producerScalarCarriersMayRemainMerelyCorresponding : Bool
    producerScalarCarriersMayRemainMerelyCorrespondingIsFalse :
      producerScalarCarriersMayRemainMerelyCorresponding ≡ false

    universalTaperMustBeSameAcrossAllChannels : Bool
    universalTaperMustBeSameAcrossAllChannelsIsTrue :
      universalTaperMustBeSameAcrossAllChannels ≡ true

    finalStrictInequalityMustLiveOnOneOrderedScalarCarrier : Bool
    finalStrictInequalityMustLiveOnOneOrderedScalarCarrierIsTrue :
      finalStrictInequalityMustLiveOnOneOrderedScalarCarrier ≡ true

    assemblyAutomaticallyProducesContradiction : Bool
    assemblyAutomaticallyProducesContradictionIsTrue :
      assemblyAutomaticallyProducesContradiction ≡ true

    rhDerivedHereWithoutAssembly : Bool
    rhDerivedHereWithoutAssemblyIsFalse : rhDerivedHereWithoutAssembly ≡ false

    highestAlphaReading : String

canonicalFinalSplitSameObjectBoundary : FinalSplitSameObjectBoundary
canonicalFinalSplitSameObjectBoundary =
  final-split-same-object-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    "The final split-complement algebra is already closed. The remaining assembly must not combine numerically corresponding values from unrelated scalar/taper carriers. Transport the literal off-ordinate, Gamma and cluster producer values into one OrderedAdditiveComplementSurface scalar, prove their universal pole-quotient tapers are the same object, then prove the exact balance, three channel bounds and B_off + B_Gamma < M_cluster on that one ordered carrier. From that package SplitPoleQuotientComplementMargin and the contradiction are compiler output. RH is not derived without those inputs."
