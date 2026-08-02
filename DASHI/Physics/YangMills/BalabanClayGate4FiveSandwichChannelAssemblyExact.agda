module DASHI.Physics.YangMills.BalabanClayGate4FiveSandwichChannelAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline
import DASHI.Physics.YangMills.BalabanClayGate4SandwichOperatorToFormBoundExact as Sandwich
import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact as Five

------------------------------------------------------------------------
-- Assemble the audited five-channel form interface from factorized norm data.
--
-- Curvature, transport, chart, gauge and constraint are each represented by a
-- three-stage sandwich. Their unit-state form bounds are derived from the
-- stage norms. The only joint physical input retained here is the exact
-- triangle inequality for the sum operator.
------------------------------------------------------------------------

record FiveSandwichChannelAssembly
    (Operator State Bound : Set) : Set₂ where
  field
    operatorAlgebra : Pipeline.OperatorNormAlgebra Operator Bound
    formAlgebra : Sandwich.OperatorNormFormAlgebra
      Operator State Bound operatorAlgebra

    total : Operator

    curvatureBudget transportBudget chartBudget gaugeBudget constraintBudget :
      Sandwich.SandwichChannelNormBudget formAlgebra

    addBound : Bound → Bound → Bound
    addMonotone : ∀ {left leftUpper right rightUpper} →
      Pipeline.LessEqual operatorAlgebra left leftUpper →
      Pipeline.LessEqual operatorAlgebra right rightUpper →
      Pipeline.LessEqual operatorAlgebra
        (addBound left right) (addBound leftUpper rightUpper)

    epsilonTotal : Bound
    epsilonTotalMeaning :
      epsilonTotal
      ≡ addBound (Sandwich.epsilon curvatureBudget)
          (addBound (Sandwich.epsilon transportBudget)
            (addBound (Sandwich.epsilon chartBudget)
              (addBound
                (Sandwich.epsilon gaugeBudget)
                (Sandwich.epsilon constraintBudget))))

    totalFormTriangle : ∀ state →
      Sandwich.UnitState formAlgebra state →
      Pipeline.LessEqual operatorAlgebra
        (Sandwich.absolute formAlgebra
          (Sandwich.inner formAlgebra state
            (Sandwich.apply formAlgebra total state)))
        (addBound
          (Sandwich.absolute formAlgebra
            (Sandwich.inner formAlgebra state
              (Sandwich.apply formAlgebra
                (Sandwich.channel curvatureBudget) state)))
          (addBound
            (Sandwich.absolute formAlgebra
              (Sandwich.inner formAlgebra state
                (Sandwich.apply formAlgebra
                  (Sandwich.channel transportBudget) state)))
            (addBound
              (Sandwich.absolute formAlgebra
                (Sandwich.inner formAlgebra state
                  (Sandwich.apply formAlgebra
                    (Sandwich.channel chartBudget) state)))
              (addBound
                (Sandwich.absolute formAlgebra
                  (Sandwich.inner formAlgebra state
                    (Sandwich.apply formAlgebra
                      (Sandwich.channel gaugeBudget) state)))
                (Sandwich.absolute formAlgebra
                  (Sandwich.inner formAlgebra state
                    (Sandwich.apply formAlgebra
                      (Sandwich.channel constraintBudget) state)))))))

    TotalRemainderMeaning : Operator → Set
    totalRemainderMeaning : TotalRemainderMeaning total

open FiveSandwichChannelAssembly public

asFiveChannelFormBoundData :
  ∀ {Operator State Bound} →
  FiveSandwichChannelAssembly Operator State Bound →
  Five.FiveChannelFormBoundData Operator State Bound
asFiveChannelFormBoundData assembly = record
  { Five.FiveChannelFormBoundData.total = total assembly
  ; Five.FiveChannelFormBoundData.curvature =
      Sandwich.channel (curvatureBudget assembly)
  ; Five.FiveChannelFormBoundData.transport =
      Sandwich.channel (transportBudget assembly)
  ; Five.FiveChannelFormBoundData.chart =
      Sandwich.channel (chartBudget assembly)
  ; Five.FiveChannelFormBoundData.gauge =
      Sandwich.channel (gaugeBudget assembly)
  ; Five.FiveChannelFormBoundData.constraint =
      Sandwich.channel (constraintBudget assembly)
  ; Five.FiveChannelFormBoundData.formAbsolute =
      λ operator state →
        Sandwich.absolute (formAlgebra assembly)
          (Sandwich.inner (formAlgebra assembly) state
            (Sandwich.apply (formAlgebra assembly) operator state))
  ; Five.FiveChannelFormBoundData.epsilonCurvature =
      Sandwich.epsilon (curvatureBudget assembly)
  ; Five.FiveChannelFormBoundData.epsilonTransport =
      Sandwich.epsilon (transportBudget assembly)
  ; Five.FiveChannelFormBoundData.epsilonChart =
      Sandwich.epsilon (chartBudget assembly)
  ; Five.FiveChannelFormBoundData.epsilonGauge =
      Sandwich.epsilon (gaugeBudget assembly)
  ; Five.FiveChannelFormBoundData.epsilonConstraint =
      Sandwich.epsilon (constraintBudget assembly)
  ; Five.FiveChannelFormBoundData.epsilonTotal = epsilonTotal assembly
  ; Five.FiveChannelFormBoundData.add = addBound assembly
  ; Five.FiveChannelFormBoundData.LessEqual =
      Pipeline.LessEqual (operatorAlgebra assembly)
  ; Five.FiveChannelFormBoundData.UnitState =
      Sandwich.UnitState (formAlgebra assembly)
  ; Five.FiveChannelFormBoundData.transitive =
      Pipeline.transitive (operatorAlgebra assembly)
  ; Five.FiveChannelFormBoundData.addMonotone = addMonotone assembly
  ; Five.FiveChannelFormBoundData.epsilonTotalMeaning =
      epsilonTotalMeaning assembly
  ; Five.FiveChannelFormBoundData.totalFormTriangle =
      totalFormTriangle assembly
  ; Five.FiveChannelFormBoundData.curvatureFormBound =
      Sandwich.sandwichChannelUnitFormBound
        (curvatureBudget assembly)
  ; Five.FiveChannelFormBoundData.transportFormBound =
      Sandwich.sandwichChannelUnitFormBound
        (transportBudget assembly)
  ; Five.FiveChannelFormBoundData.chartFormBound =
      Sandwich.sandwichChannelUnitFormBound (chartBudget assembly)
  ; Five.FiveChannelFormBoundData.gaugeFormBound =
      Sandwich.sandwichChannelUnitFormBound (gaugeBudget assembly)
  ; Five.FiveChannelFormBoundData.constraintFormBound =
      Sandwich.sandwichChannelUnitFormBound
        (constraintBudget assembly)
  ; Five.FiveChannelFormBoundData.TotalRemainderMeaning =
      TotalRemainderMeaning assembly
  ; Five.FiveChannelFormBoundData.totalRemainderMeaning =
      totalRemainderMeaning assembly
  }

fiveSandwichChannelFormAssemblyLevel : ProofLevel
fiveSandwichChannelFormAssemblyLevel = machineChecked

physicalFiveChannelTotalTriangleInputsLevel : ProofLevel
physicalFiveChannelTotalTriangleInputsLevel = conditional

physicalFiveChannelStageNormBudgetsInputsLevel : ProofLevel
physicalFiveChannelStageNormBudgetsInputsLevel = conditional
