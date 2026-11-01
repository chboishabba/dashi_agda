module DASHI.Physics.YangMills.BalabanClayGate4SandwichOperatorToFormBoundExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline

------------------------------------------------------------------------
-- Factorized Hessian channel bounds from operator norms.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- For a unit vector v and E = D* C D,
--
--   |<v,Ev>| <= ||E|| <= ||D*|| ||C|| ||D||.
--
-- The composition estimate is supplied by the existing operator-norm pipeline;
-- this module packages the three-stage product as the literal channel epsilon.
------------------------------------------------------------------------

record OperatorNormFormAlgebra
    (Operator State Bound : Set)
    (operatorAlgebra : Pipeline.OperatorNormAlgebra Operator Bound) : Set₁ where
  field
    apply : Operator → State → State
    inner : State → State → Bound
    absolute : Bound → Bound
    UnitState : State → Set

    -- Standard finite-dimensional norm-to-form inequality, usually obtained
    -- from Cauchy--Schwarz and ||Av|| <= ||A|| ||v||.
    unitFormBelowOperatorNorm : ∀ operator state →
      UnitState state →
      Pipeline.LessEqual operatorAlgebra
        (absolute (inner state (apply operator state)))
        (Pipeline.operatorNorm operatorAlgebra operator)

open OperatorNormFormAlgebra public

record SandwichChannelNormBudget
    {Operator State Bound : Set}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator Bound}
    (formAlgebra : OperatorNormFormAlgebra
      Operator State Bound operatorAlgebra) : Set₁ where
  field
    leftLeg middle rightLeg channel : Operator
    leftBound middleBound rightBound epsilon : Bound

    channelMeaning :
      channel
      ≡ Pipeline.threeStageComposition operatorAlgebra
          leftLeg middle rightLeg

    leftEstimate :
      Pipeline.LessEqual operatorAlgebra
        (Pipeline.operatorNorm operatorAlgebra leftLeg) leftBound
    middleEstimate :
      Pipeline.LessEqual operatorAlgebra
        (Pipeline.operatorNorm operatorAlgebra middle) middleBound
    rightEstimate :
      Pipeline.LessEqual operatorAlgebra
        (Pipeline.operatorNorm operatorAlgebra rightLeg) rightBound

    epsilonMeaning :
      epsilon
      ≡ Pipeline.multiply operatorAlgebra leftBound
          (Pipeline.multiply operatorAlgebra middleBound rightBound)

open SandwichChannelNormBudget public

sandwichChannelOperatorNormBound :
  ∀ {Operator State Bound}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator Bound}
    {formAlgebra : OperatorNormFormAlgebra
      Operator State Bound operatorAlgebra}
    (budget : SandwichChannelNormBudget formAlgebra) →
  Pipeline.LessEqual operatorAlgebra
    (Pipeline.operatorNorm operatorAlgebra (channel budget))
    (epsilon budget)
sandwichChannelOperatorNormBound
    {operatorAlgebra = operatorAlgebra} budget =
  subst
    (λ selected →
      Pipeline.LessEqual operatorAlgebra
        (Pipeline.operatorNorm operatorAlgebra selected)
        (epsilon budget))
    (sym (channelMeaning budget))
    (subst
      (λ selected →
        Pipeline.LessEqual operatorAlgebra
          (Pipeline.operatorNorm operatorAlgebra
            (Pipeline.threeStageComposition operatorAlgebra
              (leftLeg budget) (middle budget) (rightLeg budget)))
          selected)
      (sym (epsilonMeaning budget))
      (Pipeline.threeStageNormBound operatorAlgebra
        (leftLeg budget) (middle budget) (rightLeg budget)
        (leftBound budget) (middleBound budget) (rightBound budget)
        (leftEstimate budget) (middleEstimate budget) (rightEstimate budget)))

sandwichChannelUnitFormBound :
  ∀ {Operator State Bound}
    {operatorAlgebra : Pipeline.OperatorNormAlgebra Operator Bound}
    {formAlgebra : OperatorNormFormAlgebra
      Operator State Bound operatorAlgebra}
    (budget : SandwichChannelNormBudget formAlgebra)
    state → UnitState formAlgebra state →
  Pipeline.LessEqual operatorAlgebra
    (absolute formAlgebra
      (inner formAlgebra state
        (apply formAlgebra (channel budget) state)))
    (epsilon budget)
sandwichChannelUnitFormBound
    {operatorAlgebra = operatorAlgebra}
    {formAlgebra = formAlgebra} budget state unit =
  Pipeline.transitive operatorAlgebra
    (unitFormBelowOperatorNorm formAlgebra
      (channel budget) state unit)
    (sandwichChannelOperatorNormBound budget)

sandwichOperatorNormProductLevel : ProofLevel
sandwichOperatorNormProductLevel = machineChecked

sandwichUnitFormProductLevel : ProofLevel
sandwichUnitFormProductLevel = machineChecked

physicalFiveChannelStageNormInputsLevel : ProofLevel
physicalFiveChannelStageNormInputsLevel = conditional
