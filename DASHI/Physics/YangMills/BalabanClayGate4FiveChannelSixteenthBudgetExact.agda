module DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSixteenthBudgetExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSelfAdjointOperatorBoundExact as Five
import DASHI.Physics.YangMills.BalabanClayGate4SelfAdjointFormOperatorNormExact as FormNorm

------------------------------------------------------------------------
-- Explicit epsilon allocation: five channels at one sixteenth each.
--
-- The target is intentionally conservative:
--
--   epsilon_j <= 1/16  for j = 1,...,5,
--   epsilon_total <= 5/16 < 1/2.
--
-- The same total epsilon can then be used for coercivity, inverse stability,
-- relative spectrum, determinant control and random-walk convergence.  The
-- physical work is proving each literal channel form estimate; addition and
-- the half-budget conclusion are no longer independent assumptions.
------------------------------------------------------------------------

record SixteenthBudgetAlgebra (Bound : Set) : Set₁ where
  field
    oneSixteenth twoSixteenths threeSixteenths
      fourSixteenths fiveSixteenths half : Bound

    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    twoMeaning :
      add oneSixteenth oneSixteenth ≡ twoSixteenths
    threeMeaning :
      add oneSixteenth twoSixteenths ≡ threeSixteenths
    fourMeaning :
      add oneSixteenth threeSixteenths ≡ fourSixteenths
    fiveMeaning :
      add oneSixteenth fourSixteenths ≡ fiveSixteenths

    fiveBelowHalf : LessEqual fiveSixteenths half

open SixteenthBudgetAlgebra public

nestedFiveSixteenths :
  ∀ {Bound} (algebra : SixteenthBudgetAlgebra Bound) →
  add algebra (oneSixteenth algebra)
    (add algebra (oneSixteenth algebra)
      (add algebra (oneSixteenth algebra)
        (add algebra (oneSixteenth algebra)
          (oneSixteenth algebra))))
  ≡ fiveSixteenths algebra
nestedFiveSixteenths algebra
  rewrite twoMeaning algebra
        | threeMeaning algebra
        | fourMeaning algebra
        | fiveMeaning algebra =
  refl

record FiveChannelSixteenthAllocation
    {Operator State Bound : Set}
    (dataSet : Five.FiveChannelFormBoundData Operator State Bound) : Set₁ where
  field
    budget : SixteenthBudgetAlgebra Bound

    physicalNestedFiveMeaning :
      Five.add dataSet (oneSixteenth budget)
        (Five.add dataSet (oneSixteenth budget)
          (Five.add dataSet (oneSixteenth budget)
            (Five.add dataSet (oneSixteenth budget)
              (oneSixteenth budget))))
      ≡ fiveSixteenths budget

    physicalFiveBelowHalf :
      Five.LessEqual dataSet
        (fiveSixteenths budget) (half budget)

    curvatureBelowSixteenth :
      Five.LessEqual dataSet
        (Five.epsilonCurvature dataSet) (oneSixteenth budget)
    transportBelowSixteenth :
      Five.LessEqual dataSet
        (Five.epsilonTransport dataSet) (oneSixteenth budget)
    chartBelowSixteenth :
      Five.LessEqual dataSet
        (Five.epsilonChart dataSet) (oneSixteenth budget)
    gaugeBelowSixteenth :
      Five.LessEqual dataSet
        (Five.epsilonGauge dataSet) (oneSixteenth budget)
    constraintBelowSixteenth :
      Five.LessEqual dataSet
        (Five.epsilonConstraint dataSet) (oneSixteenth budget)

open FiveChannelSixteenthAllocation public

epsilonTotalBelowFiveSixteenths :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound} →
  (allocation : FiveChannelSixteenthAllocation dataSet) →
  Five.LessEqual dataSet
    (Five.epsilonTotal dataSet)
    (fiveSixteenths (budget allocation))
epsilonTotalBelowFiveSixteenths {dataSet = dataSet} allocation =
  subst
    (λ upper → Five.LessEqual dataSet
      (Five.epsilonTotal dataSet) upper)
    (physicalNestedFiveMeaning allocation)
    (subst
      (λ selectedTotal →
        Five.LessEqual dataSet selectedTotal
          (Five.add dataSet (oneSixteenth (budget allocation))
            (Five.add dataSet (oneSixteenth (budget allocation))
              (Five.add dataSet (oneSixteenth (budget allocation))
                (Five.add dataSet (oneSixteenth (budget allocation))
                  (oneSixteenth (budget allocation)))))))
      (sym (Five.epsilonTotalMeaning dataSet))
      (Five.addMonotone dataSet
        (curvatureBelowSixteenth allocation)
        (Five.addMonotone dataSet
          (transportBelowSixteenth allocation)
          (Five.addMonotone dataSet
            (chartBelowSixteenth allocation)
            (Five.addMonotone dataSet
              (gaugeBelowSixteenth allocation)
              (constraintBelowSixteenth allocation))))))

epsilonTotalBelowHalf :
  ∀ {Operator State Bound}
    {dataSet : Five.FiveChannelFormBoundData Operator State Bound} →
  (allocation : FiveChannelSixteenthAllocation dataSet) →
  Five.LessEqual dataSet
    (Five.epsilonTotal dataSet)
    (half (budget allocation))
epsilonTotalBelowHalf {dataSet = dataSet} allocation =
  Five.transitive dataSet
    (epsilonTotalBelowFiveSixteenths allocation)
    (physicalFiveBelowHalf allocation)

selfAdjointRemainderNormBelowHalf :
  ∀ {Operator State Bound}
    (meaning : Five.FiveChannelSelfAdjointNormMeaning
      Operator State Bound)
    (allocation : FiveChannelSixteenthAllocation
      (Five.formData meaning)) →
  FormNorm.LessEqual (Five.normData meaning)
    (FormNorm.operatorNorm (Five.normData meaning)
      (Five.total (Five.formData meaning)))
    (half (budget allocation))
selfAdjointRemainderNormBelowHalf meaning allocation =
  FormNorm.transitive (Five.normData meaning)
    (Five.fiveChannelSelfAdjointOperatorNormBelowTotal meaning)
    (subst
      (λ proposition → proposition)
      (sym
        (Five.orderMeaning meaning
          (Five.epsilonTotal (Five.formData meaning))
          (half (budget allocation))))
      (epsilonTotalBelowHalf allocation))

fiveChannelSixteenthArithmeticLevel : ProofLevel
fiveChannelSixteenthArithmeticLevel = machineChecked

fiveChannelTotalBelowHalfLevel : ProofLevel
fiveChannelTotalBelowHalfLevel = machineChecked

fiveChannelSelfAdjointNormBelowHalfLevel : ProofLevel
fiveChannelSelfAdjointNormBelowHalfLevel = machineChecked

physicalChannelOneSixteenthEstimatesInputsLevel : ProofLevel
physicalChannelOneSixteenthEstimatesInputsLevel = conditional

physicalSixteenthScalarInterpretationInputsLevel : ProofLevel
physicalSixteenthScalarInterpretationInputsLevel = conditional
