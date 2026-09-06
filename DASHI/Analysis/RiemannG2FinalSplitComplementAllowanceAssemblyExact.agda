module DASHI.Analysis.RiemannG2FinalSplitComplementAllowanceAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannG2PoleQuotientChannelAllowanceExact as Allowance
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster

------------------------------------------------------------------------
-- ALLOWANCE-AWARE FINAL SAME-OBJECT ASSEMBLY
--
-- The older same-object assembly correctly requires one scalar carrier and one
-- literal universal pole-quotient taper, but it takes
--
--   B_off + B_Gamma < M_cluster
--
-- as an input.  The new channel-allowance compiler derives that strict input
-- from consumer-selected allowances.  This owner joins the two surfaces so that
-- no post-analysis strict-budget theorem has to be reproved separately.
------------------------------------------------------------------------

record FinalSplitComplementAllowanceAssembly
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
      Existing.cast offGammaTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Gamma.universalPoleQuotientTaper gamma

    sameUniversalTaperOffCluster :
      Existing.cast offClusterTaperCarrierIdentity
        (Off.universalPoleQuotientTaper off)
      ≡ Cluster.universalPoleQuotientTaper cluster

    offOrdinateResponse : FinalScalar
    offOrdinateResponseIsProducer :
      offOrdinateResponse
      ≡ Existing.cast offScalarIdentity
          (Off.OffOrdinateResponse off (Off.universalPoleQuotientTaper off))

    offOrdinateBudget : FinalScalar
    offOrdinateBudgetIsProducer :
      offOrdinateBudget
      ≡ Existing.cast offScalarIdentity
          (Off.OffOrdinateBudget off (Off.universalPoleQuotientTaper off))

    gammaResidual : FinalScalar
    gammaResidualIsProducer :
      gammaResidual
      ≡ Existing.cast gammaScalarIdentity
          (Gamma.GammaResponse gamma (Gamma.universalPoleQuotientTaper gamma))

    gammaBudget : FinalScalar
    gammaBudgetIsProducer :
      gammaBudget
      ≡ Existing.cast gammaScalarIdentity
          (Gamma.GammaBudget gamma (Gamma.universalPoleQuotientTaper gamma))

    clusterResponse : FinalScalar
    clusterResponseIsProducer :
      clusterResponse
      ≡ Existing.cast clusterScalarIdentity
          (Cluster.ClusterResponse cluster (Cluster.universalPoleQuotientTaper cluster))

    clusterMargin : FinalScalar
    clusterMarginIsProducer :
      clusterMargin
      ≡ Existing.cast clusterScalarIdentity
          (Cluster.ClusterMargin cluster (Cluster.universalPoleQuotientTaper cluster))

    clusterEqualsOffPlusGamma :
      clusterResponse ≡ Split.add surface offOrdinateResponse gammaResidual

    clusterMarginLower :
      Complement._≤_ (Split.order surface) clusterMargin clusterResponse

    offOrdinateUpper :
      Complement._≤_ (Split.order surface) offOrdinateResponse offOrdinateBudget

    gammaUpper :
      Complement._≤_ (Split.order surface) gammaResidual gammaBudget

    -- Consumer-selected final allowances.
    offAllowance gammaAllowance : FinalScalar

    offBudgetBelowAllowance :
      Complement._≤_ (Split.order surface) offOrdinateBudget offAllowance

    gammaBudgetBelowAllowance :
      Complement._≤_ (Split.order surface) gammaBudget gammaAllowance

    allowancesStrictBelowMargin :
      Complement._<_ (Split.order surface)
        (Split.add surface offAllowance gammaAllowance)
        clusterMargin

    assemblyReference : String

open FinalSplitComplementAllowanceAssembly public

------------------------------------------------------------------------
-- Compiler to the already-owned generic allowance layer.
------------------------------------------------------------------------

assemblyToInputsExceptStrictBudget :
  ∀ {surface off gamma cluster} →
  FinalSplitComplementAllowanceAssembly surface off gamma cluster →
  Allowance.SplitInputsExceptStrictBudget surface
assemblyToInputsExceptStrictBudget assembly = record
  { Allowance.clusterResponse = clusterResponse assembly
  ; Allowance.offOrdinateResponse = offOrdinateResponse assembly
  ; Allowance.gammaResidual = gammaResidual assembly
  ; Allowance.offOrdinateBudget = offOrdinateBudget assembly
  ; Allowance.gammaBudget = gammaBudget assembly
  ; Allowance.clusterMargin = clusterMargin assembly
  ; Allowance.clusterEqualsOffPlusGamma = clusterEqualsOffPlusGamma assembly
  ; Allowance.clusterMarginLower = clusterMarginLower assembly
  ; Allowance.offOrdinateUpper = offOrdinateUpper assembly
  ; Allowance.gammaUpper = gammaUpper assembly
  }

assemblyToChannelAllowance :
  ∀ {surface off gamma cluster} →
  FinalSplitComplementAllowanceAssembly surface off gamma cluster →
  Allowance.PoleQuotientChannelAllowance surface
assemblyToChannelAllowance assembly = record
  { Allowance.offBudget = offOrdinateBudget assembly
  ; Allowance.gammaBudget = gammaBudget assembly
  ; Allowance.offAllowance = offAllowance assembly
  ; Allowance.gammaAllowance = gammaAllowance assembly
  ; Allowance.clusterMargin = clusterMargin assembly
  ; Allowance.offBudgetBelowAllowance = offBudgetBelowAllowance assembly
  ; Allowance.gammaBudgetBelowAllowance = gammaBudgetBelowAllowance assembly
  ; Allowance.allowancesStrictBelowMargin = allowancesStrictBelowMargin assembly
  }

assemblyToSplitComplementMargin :
  ∀ {surface off gamma cluster} →
  FinalSplitComplementAllowanceAssembly surface off gamma cluster →
  Split.SplitPoleQuotientComplementMargin surface
assemblyToSplitComplementMargin assembly =
  Allowance.allowanceToSplitComplementMargin
    (assemblyToInputsExceptStrictBudget assembly)
    (assemblyToChannelAllowance assembly)
    refl refl refl

assemblyContradiction :
  ∀ {surface off gamma cluster} →
  FinalSplitComplementAllowanceAssembly surface off gamma cluster →
  ⊥
assemblyContradiction {surface} assembly =
  Split.splitPoleQuotientComplementContradiction surface
    (assemblyToSplitComplementMargin assembly)

------------------------------------------------------------------------
-- Boundary / scheduling interpretation.
------------------------------------------------------------------------

record FinalAllowanceAssemblyBoundary : Set where
  constructor final-allowance-assembly-boundary
  field
    strictCombinedBudgetIsFreshPostAnalysisLeaf : Bool
    strictCombinedBudgetIsFreshPostAnalysisLeafIsFalse :
      strictCombinedBudgetIsFreshPostAnalysisLeaf ≡ false

    sameObjectTransportStillRequired : Bool
    sameObjectTransportStillRequiredIsTrue :
      sameObjectTransportStillRequired ≡ true

    consumerAllowanceFitStillRequired : Bool
    consumerAllowanceFitStillRequiredIsTrue :
      consumerAllowanceFitStillRequired ≡ true

    allowanceAssemblyAutomaticallyProducesContradiction : Bool
    allowanceAssemblyAutomaticallyProducesContradictionIsTrue :
      allowanceAssemblyAutomaticallyProducesContradiction ≡ true

    rhDerivedWithoutLiteralProducerAssembly : Bool
    rhDerivedWithoutLiteralProducerAssemblyIsFalse :
      rhDerivedWithoutLiteralProducerAssembly ≡ false

    boundedReading : String

canonicalFinalAllowanceAssemblyBoundary : FinalAllowanceAssemblyBoundary
canonicalFinalAllowanceAssemblyBoundary =
  final-allowance-assembly-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    "After literal Off/Gamma/Cluster producers are transported to one ordered scalar and one universal pole-quotient taper, the final consumer chooses A_off and A_Gamma, proves B_off <= A_off, B_Gamma <= A_Gamma and A_off + A_Gamma < M_cluster, and this owner compiles those receipts directly into the existing split-complement contradiction. The strict combined-budget theorem is no longer a separate research leaf. Same-object transport and the actual analytic allowance fits remain required. RH is not derived without those literal inputs."
