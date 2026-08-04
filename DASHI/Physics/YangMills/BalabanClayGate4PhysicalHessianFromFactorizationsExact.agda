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
  { algebra =
      formAlgebra inputs
  ; referenceHessian =
      referenceHessian inputs
  ; fullHessian =
      fullHessian inputs
  ; totalRemainder =
      totalRemainder inputs
  ; curvature =
      Factor.curvature (factorizations inputs)
  ; transport =
      Factor.transport (factorizations inputs)
  ; chart =
      Factor.chart (factorizations inputs)
  ; gauge =
      Factor.gauge (factorizations inputs)
  ; constraint =
      Factor.constraint (factorizations inputs)
  ; totalRemainderMeaning =
      totalRemainderMeaning inputs
  ; fullHessianMeaning =
      fullHessianMeaning inputs
  ; referenceSelfAdjoint =
      referenceSelfAdjoint inputs
  ; curvatureSelfAdjoint =
      transportFactorSelfAdjoint inputs
        (Factor.curvature (factorizations inputs))
        (Factor.curvatureSelfAdjointFromFactorization
          (factorizations inputs))
  ; transportSelfAdjoint =
      transportFactorSelfAdjoint inputs
        (Factor.transport (factorizations inputs))
        (Factor.transportSelfAdjointFromFactorization
          (factorizations inputs))
  ; chartSelfAdjoint =
      transportFactorSelfAdjoint inputs
        (Factor.chart (factorizations inputs))
        (Factor.chartSelfAdjointFromFactorization
          (factorizations inputs))
  ; gaugeSelfAdjoint =
      transportFactorSelfAdjoint inputs
        (Factor.gauge (factorizations inputs))
        (Factor.gaugeSelfAdjointFromFactorization
          (factorizations inputs))
  ; constraintSelfAdjoint =
      transportFactorSelfAdjoint inputs
        (Factor.constraint (factorizations inputs))
        (Factor.constraintSelfAdjointFromFactorization
          (factorizations inputs))
  ; channelIdentification =
      channelIdentification inputs
  ; curvatureChannelMeaning =
      curvatureChannelMeaning inputs
  ; transportChannelMeaning =
      transportChannelMeaning inputs
  ; chartChannelMeaning =
      chartChannelMeaning inputs
  ; gaugeChannelMeaning =
      gaugeChannelMeaning inputs
  ; constraintChannelMeaning =
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
