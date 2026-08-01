module DASHI.Physics.YangMills.BalabanClayGate4PhysicalHessianFiveChannelDecompositionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSumSelfAdjointExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalOperatorChannelIdentificationExact as Channels

------------------------------------------------------------------------
-- Literal constrained-Hessian ownership by the five audited T3 channels.
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
-- The physical proof must differentiate one selected Wilson + gauge-fixing +
-- constraint functional and identify every resulting summand exactly once.
-- This record makes that requirement literal: the full Hessian is the reference
-- Hessian plus an audited five-channel remainder, and the same operator values
-- inhabit the exhaustive channel map used by T3.
------------------------------------------------------------------------

record PhysicalHessianFiveChannelDecomposition
    (Operator State Bound : Set) : Set₁ where
  field
    algebra : Five.OperatorFormSumAlgebra Operator State Bound

    referenceHessian fullHessian totalRemainder : Operator
    curvature transport chart gauge constraint : Operator

    totalRemainderMeaning :
      totalRemainder
      ≡ Five.addOperator algebra curvature
          (Five.addOperator algebra transport
            (Five.addOperator algebra chart
              (Five.addOperator algebra gauge constraint)))

    fullHessianMeaning :
      fullHessian
      ≡ Five.addOperator algebra referenceHessian totalRemainder

    referenceSelfAdjoint : Five.SelfAdjoint algebra referenceHessian
    curvatureSelfAdjoint : Five.SelfAdjoint algebra curvature
    transportSelfAdjoint : Five.SelfAdjoint algebra transport
    chartSelfAdjoint : Five.SelfAdjoint algebra chart
    gaugeSelfAdjoint : Five.SelfAdjoint algebra gauge
    constraintSelfAdjoint : Five.SelfAdjoint algebra constraint

    channelIdentification :
      Channels.PhysicalChannelOperatorIdentification Operator

    curvatureChannelMeaning :
      Channels.t3Operator channelIdentification Channels.curvature
      ≡ curvature
    transportChannelMeaning :
      Channels.t3Operator channelIdentification Channels.transport
      ≡ transport
    chartChannelMeaning :
      Channels.t3Operator channelIdentification Channels.chart
      ≡ chart
    gaugeChannelMeaning :
      Channels.t3Operator channelIdentification Channels.gauge
      ≡ gauge
    constraintChannelMeaning :
      Channels.t3Operator channelIdentification Channels.constraint
      ≡ constraint

open PhysicalHessianFiveChannelDecomposition public

asFiveChannelOperatorSum :
  ∀ {Operator State Bound} →
  PhysicalHessianFiveChannelDecomposition Operator State Bound →
  Five.FiveChannelOperatorSum Operator State Bound
asFiveChannelOperatorSum dataSet = record
  { Five.FiveChannelOperatorSum.algebra = algebra dataSet
  ; Five.FiveChannelOperatorSum.total = totalRemainder dataSet
  ; Five.FiveChannelOperatorSum.curvature = curvature dataSet
  ; Five.FiveChannelOperatorSum.transport = transport dataSet
  ; Five.FiveChannelOperatorSum.chart = chart dataSet
  ; Five.FiveChannelOperatorSum.gauge = gauge dataSet
  ; Five.FiveChannelOperatorSum.constraint = constraint dataSet
  ; Five.FiveChannelOperatorSum.totalMeaning = totalRemainderMeaning dataSet
  ; Five.FiveChannelOperatorSum.curvatureSelfAdjoint =
      curvatureSelfAdjoint dataSet
  ; Five.FiveChannelOperatorSum.transportSelfAdjoint =
      transportSelfAdjoint dataSet
  ; Five.FiveChannelOperatorSum.chartSelfAdjoint = chartSelfAdjoint dataSet
  ; Five.FiveChannelOperatorSum.gaugeSelfAdjoint = gaugeSelfAdjoint dataSet
  ; Five.FiveChannelOperatorSum.constraintSelfAdjoint =
      constraintSelfAdjoint dataSet
  }

totalRemainderSelfAdjoint :
  ∀ {Operator State Bound}
    (dataSet : PhysicalHessianFiveChannelDecomposition
      Operator State Bound) →
  Five.SelfAdjoint (algebra dataSet) (totalRemainder dataSet)
totalRemainderSelfAdjoint dataSet =
  Five.totalFiveChannelSelfAdjoint (asFiveChannelOperatorSum dataSet)

fullHessianSelfAdjoint :
  ∀ {Operator State Bound}
    (dataSet : PhysicalHessianFiveChannelDecomposition
      Operator State Bound) →
  Five.SelfAdjoint (algebra dataSet) (fullHessian dataSet)
fullHessianSelfAdjoint dataSet =
  subst
    (Five.SelfAdjoint (algebra dataSet))
    (sym (fullHessianMeaning dataSet))
    (Five.selfAdjointAdd (algebra dataSet)
      (referenceHessian dataSet)
      (totalRemainder dataSet)
      (referenceSelfAdjoint dataSet)
      (totalRemainderSelfAdjoint dataSet))

totalRemainderFormTriangle :
  ∀ {Operator State Bound}
    (dataSet : PhysicalHessianFiveChannelDecomposition
      Operator State Bound)
    state →
  Five.LessEqual (algebra dataSet)
    (Five.quadraticFormAbsolute (algebra dataSet)
      (totalRemainder dataSet) state)
    (Five.addBound (algebra dataSet)
      (Five.quadraticFormAbsolute (algebra dataSet)
        (curvature dataSet) state)
      (Five.addBound (algebra dataSet)
        (Five.quadraticFormAbsolute (algebra dataSet)
          (transport dataSet) state)
        (Five.addBound (algebra dataSet)
          (Five.quadraticFormAbsolute (algebra dataSet)
            (chart dataSet) state)
          (Five.addBound (algebra dataSet)
            (Five.quadraticFormAbsolute (algebra dataSet)
              (gauge dataSet) state)
            (Five.quadraticFormAbsolute (algebra dataSet)
              (constraint dataSet) state)))))
totalRemainderFormTriangle dataSet =
  Five.totalFiveChannelFormTriangle (asFiveChannelOperatorSum dataSet)

physicalHessianFiveChannelAssemblyLevel : ProofLevel
physicalHessianFiveChannelAssemblyLevel = machineChecked

physicalHessianSelfAdjointAssemblyLevel : ProofLevel
physicalHessianSelfAdjointAssemblyLevel = machineChecked

physicalHessianChannelExhaustivenessLevel : ProofLevel
physicalHessianChannelExhaustivenessLevel = machineChecked

physicalWilsonSecondVariationIdentificationInputsLevel : ProofLevel
physicalWilsonSecondVariationIdentificationInputsLevel = conditional

physicalGaugeConstraintSecondVariationInputsLevel : ProofLevel
physicalGaugeConstraintSecondVariationInputsLevel = conditional
