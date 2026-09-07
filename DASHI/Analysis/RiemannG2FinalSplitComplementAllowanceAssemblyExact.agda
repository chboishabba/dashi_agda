module DASHI.Analysis.RiemannG2FinalSplitComplementAllowanceAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement
import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannG2PoleQuotientChannelAllowanceExact as Allowance
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as ProducerAllowance
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Existing
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateBudgetTargetExact as Off
import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact as Cluster

------------------------------------------------------------------------
-- ALLOWANCE-AWARE FINAL SAME-OBJECT ASSEMBLY
--
-- This version consumes the producer-facing allowance payments themselves.
-- Therefore final A_off / A_Gamma are literal transports of the allowances the
-- analytic Off/Gamma proofs were assigned; the final assembly cannot silently
-- substitute a different pair of allowances after those proofs are complete.
------------------------------------------------------------------------

record FinalSplitComplementAllowanceAssembly
    (surface : Split.OrderedAdditiveComplementSurface)
    (offPayment : ProducerAllowance.PoleQuotientOffAllowancePayment)
    (gammaPayment : ProducerAllowance.PoleQuotientGammaAllowancePayment)
    (cluster : Cluster.PoleQuotientClusterMarginTarget) : Set₁ where
  private
    off = ProducerAllowance.PoleQuotientOffAllowancePayment.target offPayment
    gamma = ProducerAllowance.PoleQuotientGammaAllowancePayment.target gammaPayment
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

    -- Final allowance values are fixed by the analytic producer payments.
    offAllowance : FinalScalar
    offAllowanceIsProducerAssignment :
      offAllowance
      ≡ Existing.cast offScalarIdentity
          (ProducerAllowance.assignedOffAllowance offPayment)

    gammaAllowance : FinalScalar
    gammaAllowanceIsProducerAssignment :
      gammaAllowance
      ≡ Existing.cast gammaScalarIdentity
          (ProducerAllowance.assignedGammaAllowance gammaPayment)

    -- These are the same-order transports of the producer allowance theorems.
    -- Scalar equality alone cannot transport an order relation, so the final
    -- ordered carrier must prove these two compatibility receipts explicitly.
    offBudgetBelowAssignedAllowance :
      Complement._≤_ (Split.order surface) offOrdinateBudget offAllowance

    gammaBudgetBelowAssignedAllowance :
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
  ∀ {surface offPayment gammaPayment cluster} →
  FinalSplitComplementAllowanceAssembly
    surface offPayment gammaPayment cluster →
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
  ∀ {surface offPayment gammaPayment cluster} →
  FinalSplitComplementAllowanceAssembly
    surface offPayment gammaPayment cluster →
  Allowance.PoleQuotientChannelAllowance surface
assemblyToChannelAllowance assembly = record
  { Allowance.offBudget = offOrdinateBudget assembly
  ; Allowance.gammaBudget = gammaBudget assembly
  ; Allowance.offAllowance = offAllowance assembly
  ; Allowance.gammaAllowance = gammaAllowance assembly
  ; Allowance.clusterMargin = clusterMargin assembly
  ; Allowance.offBudgetBelowAllowance = offBudgetBelowAssignedAllowance assembly
  ; Allowance.gammaBudgetBelowAllowance = gammaBudgetBelowAssignedAllowance assembly
  ; Allowance.allowancesStrictBelowMargin = allowancesStrictBelowMargin assembly
  }

assemblyToSplitComplementMargin :
  ∀ {surface offPayment gammaPayment cluster} →
  FinalSplitComplementAllowanceAssembly
    surface offPayment gammaPayment cluster →
  Split.SplitPoleQuotientComplementMargin surface
assemblyToSplitComplementMargin assembly =
  Allowance.allowanceToSplitComplementMargin
    (assemblyToInputsExceptStrictBudget assembly)
    (assemblyToChannelAllowance assembly)
    refl refl refl

assemblyContradiction :
  ∀ {surface offPayment gammaPayment cluster} →
  FinalSplitComplementAllowanceAssembly
    surface offPayment gammaPayment cluster →
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

    finalAllowancesMayDifferFromAnalyticAssignedAllowances : Bool
    finalAllowancesMayDifferFromAnalyticAssignedAllowancesIsFalse :
      finalAllowancesMayDifferFromAnalyticAssignedAllowances ≡ false

    sameObjectTransportStillRequired : Bool
    sameObjectTransportStillRequiredIsTrue :
      sameObjectTransportStillRequired ≡ true

    sameOrderTransportOfAllowanceBoundsStillRequired : Bool
    sameOrderTransportOfAllowanceBoundsStillRequiredIsTrue :
      sameOrderTransportOfAllowanceBoundsStillRequired ≡ true

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
    false refl
    true refl
    true refl
    true refl
    false refl
    "The final assembly now consumes the actual Off/Gamma allowance-payment records. A_off and A_Gamma are literal transports of the allowances those analytic proofs were assigned, so the final consumer cannot substitute easier allowances after the fact. Scalar/taper transport and same-order transport of the two allowance inequalities remain explicit proof engineering. Once those receipts and A_off + A_Gamma < M_cluster are present, the allowance compiler and existing split-complement contradiction are automatic. RH is not derived without the literal producer inputs."
