module DASHI.Physics.YangMills.BalabanClayGate4PhysicalHessianFromFactorizationsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSumSelfAdjointExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalOperatorChannelIdentificationExact as Channels
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalHessianFactorizedSelfAdjointExact as Factor
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalHessianFiveChannelDecompositionExact as Hessian

------------------------------------------------------------------------
-- Construct the physical Hessian consumer from structural factorizations.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- This adapter removes five independent self-adjointness hypotheses.  A
-- physical implementation supplies the actual channel factorizations and the
-- literal Hessian split; self-adjointness is transported from the middle
-- operators through the star sandwiches.
------------------------------------------------------------------------

record PhysicalHessianFactorizedInputs
    (Operator State Bound : Set) : Set₁ where
  field
    formAlgebra : Five.OperatorFormSumAlgebra Operator State Bound
    factorizations : Factor.FiveChannelFactorizations Operator

    selfAdjointMeaning : ∀ operator →
      Five.SelfAdjoint formAlgebra operator
      ≡ Factor.SelfAdjoint (Factor.algebra factorizations) operator

    referenceHessian fullHessian totalRemainder : Operator
    referenceSelfAdjoint : Five.SelfAdjoint formAlgebra referenceHessian

    totalRemainderMeaning :
      totalRemainder
      ≡ Five.addOperator formAlgebra
          (Factor.curvature factorizations)
          (Five.addOperator formAlgebra
            (Factor.transport factorizations)
            (Five.addOperator formAlgebra
              (Factor.chart factorizations)
              (Five.addOperator formAlgebra
                (Factor.gauge factorizations)
                (Factor.constraint factorizations))))

    fullHessianMeaning :
      fullHessian
      ≡ Five.addOperator formAlgebra referenceHessian totalRemainder

    channelIdentification :
      Channels.PhysicalChannelOperatorIdentification Operator

    curvatureChannelMeaning :
      Channels.t3Operator channelIdentification Channels.curvature
      ≡ Factor.curvature factorizations
    transportChannelMeaning :
      Channels.t3Operator channelIdentification Channels.transport
      ≡ Factor.transport factorizations
    chartChannelMeaning :
      Channels.t3Operator channelIdentification Channels.chart
      ≡ Factor.chart factorizations
    gaugeChannelMeaning :
      Channels.t3Operator channelIdentification Channels.gauge
      ≡ Factor.gauge factorizations
    constraintChannelMeaning :
      Channels.t3Operator channelIdentification Channels.constraint
      ≡ Factor.constraint factorizations

open PhysicalHessianFactorizedInputs public

transportFactorSelfAdjoint :
  ∀ {Operator State Bound}
    (inputs : PhysicalHessianFactorizedInputs Operator State Bound)
    operator →
  Factor.SelfAdjoint (Factor.algebra (factorizations inputs)) operator →
  Five.SelfAdjoint (formAlgebra inputs) operator
transportFactorSelfAdjoint inputs operator proof =
  subst
    (λ proposition → proposition)
    (sym (selfAdjointMeaning inputs operator))
    proof

asPhysicalHessianFiveChannelDecomposition :
  ∀ {Operator State Bound} →
  PhysicalHessianFactorizedInputs Operator State Bound →
  Hessian.PhysicalHessianFiveChannelDecomposition Operator State Bound
asPhysicalHessianFiveChannelDecomposition inputs = record
  { Hessian.PhysicalHessianFiveChannelDecomposition.algebra =
      formAlgebra inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.referenceHessian =
      referenceHessian inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.fullHessian =
      fullHessian inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.totalRemainder =
      totalRemainder inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.curvature =
      Factor.curvature (factorizations inputs)
  ; Hessian.PhysicalHessianFiveChannelDecomposition.transport =
      Factor.transport (factorizations inputs)
  ; Hessian.PhysicalHessianFiveChannelDecomposition.chart =
      Factor.chart (factorizations inputs)
  ; Hessian.PhysicalHessianFiveChannelDecomposition.gauge =
      Factor.gauge (factorizations inputs)
  ; Hessian.PhysicalHessianFiveChannelDecomposition.constraint =
      Factor.constraint (factorizations inputs)
  ; Hessian.PhysicalHessianFiveChannelDecomposition.totalRemainderMeaning =
      totalRemainderMeaning inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.fullHessianMeaning =
      fullHessianMeaning inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.referenceSelfAdjoint =
      referenceSelfAdjoint inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.curvatureSelfAdjoint =
      transportFactorSelfAdjoint inputs _
        (Factor.curvatureSelfAdjointFromFactorization
          (factorizations inputs))
  ; Hessian.PhysicalHessianFiveChannelDecomposition.transportSelfAdjoint =
      transportFactorSelfAdjoint inputs _
        (Factor.transportSelfAdjointFromFactorization
          (factorizations inputs))
  ; Hessian.PhysicalHessianFiveChannelDecomposition.chartSelfAdjoint =
      transportFactorSelfAdjoint inputs _
        (Factor.chartSelfAdjointFromFactorization
          (factorizations inputs))
  ; Hessian.PhysicalHessianFiveChannelDecomposition.gaugeSelfAdjoint =
      transportFactorSelfAdjoint inputs _
        (Factor.gaugeSelfAdjointFromFactorization
          (factorizations inputs))
  ; Hessian.PhysicalHessianFiveChannelDecomposition.constraintSelfAdjoint =
      transportFactorSelfAdjoint inputs _
        (Factor.constraintSelfAdjointFromFactorization
          (factorizations inputs))
  ; Hessian.PhysicalHessianFiveChannelDecomposition.channelIdentification =
      channelIdentification inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.curvatureChannelMeaning =
      curvatureChannelMeaning inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.transportChannelMeaning =
      transportChannelMeaning inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.chartChannelMeaning =
      chartChannelMeaning inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.gaugeChannelMeaning =
      gaugeChannelMeaning inputs
  ; Hessian.PhysicalHessianFiveChannelDecomposition.constraintChannelMeaning =
      constraintChannelMeaning inputs
  }

factorizedPhysicalHessianSelfAdjoint :
  ∀ {Operator State Bound}
    (inputs : PhysicalHessianFactorizedInputs Operator State Bound) →
  Five.SelfAdjoint (formAlgebra inputs) (fullHessian inputs)
factorizedPhysicalHessianSelfAdjoint inputs =
  Hessian.fullHessianSelfAdjoint
    (asPhysicalHessianFiveChannelDecomposition inputs)

physicalHessianFromFactorizationsLevel : ProofLevel
physicalHessianFromFactorizationsLevel = machineChecked

physicalHessianFactorizedSelfAdjointLevel : ProofLevel
physicalHessianFactorizedSelfAdjointLevel = machineChecked

physicalLiteralChannelFactorizationsInputsLevel : ProofLevel
physicalLiteralChannelFactorizationsInputsLevel = conditional

physicalFullHessianSplitInputsLevel : ProofLevel
physicalFullHessianSplitInputsLevel = conditional
