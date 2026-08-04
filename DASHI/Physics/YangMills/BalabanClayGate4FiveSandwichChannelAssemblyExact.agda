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
  { total = total assembly
  ; curvature =
      Sandwich.channel (curvatureBudget assembly)
  ; transport =
      Sandwich.channel (transportBudget assembly)
  ; chart =
      Sandwich.channel (chartBudget assembly)
  ; gauge =
      Sandwich.channel (gaugeBudget assembly)
  ; constraint =
      Sandwich.channel (constraintBudget assembly)
  ; formAbsolute =
      λ operator state →
        Sandwich.absolute (formAlgebra assembly)
          (Sandwich.inner (formAlgebra assembly) state
            (Sandwich.apply (formAlgebra assembly) operator state))
  ; epsilonCurvature =
      Sandwich.epsilon (curvatureBudget assembly)
  ; epsilonTransport =
      Sandwich.epsilon (transportBudget assembly)
  ; epsilonChart =
      Sandwich.epsilon (chartBudget assembly)
  ; epsilonGauge =
      Sandwich.epsilon (gaugeBudget assembly)
  ; epsilonConstraint =
      Sandwich.epsilon (constraintBudget assembly)
  ; epsilonTotal = epsilonTotal assembly
  ; add = addBound assembly
  ; LessEqual =
      Pipeline.LessEqual (operatorAlgebra assembly)
  ; UnitState =
      Sandwich.UnitState (formAlgebra assembly)
  ; transitive =
      Pipeline.transitive (operatorAlgebra assembly)
  ; addMonotone = addMonotone assembly
  ; epsilonTotalMeaning =
      epsilonTotalMeaning assembly
  ; totalFormTriangle =
      totalFormTriangle assembly
  ; curvatureFormBound =
      Sandwich.sandwichChannelUnitFormBound
        (curvatureBudget assembly)
  ; transportFormBound =
      Sandwich.sandwichChannelUnitFormBound
        (transportBudget assembly)
  ; chartFormBound =
      Sandwich.sandwichChannelUnitFormBound (chartBudget assembly)
  ; gaugeFormBound =
      Sandwich.sandwichChannelUnitFormBound (gaugeBudget assembly)
  ; constraintFormBound =
      Sandwich.sandwichChannelUnitFormBound
        (constraintBudget assembly)
  ; TotalRemainderMeaning =
      TotalRemainderMeaning assembly
  ; totalRemainderMeaning =
      totalRemainderMeaning assembly
  }

fiveSandwichChannelFormAssemblyLevel : ProofLevel
fiveSandwichChannelFormAssemblyLevel = machineChecked

physicalFiveChannelTotalTriangleInputsLevel : ProofLevel
physicalFiveChannelTotalTriangleInputsLevel = conditional

physicalFiveChannelStageNormBudgetsInputsLevel : ProofLevel
physicalFiveChannelStageNormBudgetsInputsLevel = conditional
