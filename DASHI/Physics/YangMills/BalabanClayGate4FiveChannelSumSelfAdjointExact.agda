module DASHI.Physics.YangMills.BalabanClayGate4FiveChannelSumSelfAdjointExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Five-channel operator-sum algebra.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The finite theorem is elementary but important for the physical cut.  If the
-- total Hessian remainder is the sum of curvature, transport, chart, gauge and
-- constraint channels, then additivity supplies the total form triangle and
-- closure of self-adjoint operators under addition supplies total
-- self-adjointness.  Neither fact remains an independent analytic hypothesis.
------------------------------------------------------------------------

record OperatorFormSumAlgebra
    (Operator State Bound : Set) : Set₁ where
  field
    addOperator : Operator → Operator → Operator
    addState : State → State → State
    addBound : Bound → Bound → Bound

    apply : Operator → State → State
    inner : State → State → Bound
    absolute : Bound → Bound

    LessEqual : Bound → Bound → Set
    SelfAdjoint : Operator → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (addBound left right) (addBound lower upper)

    applyAdd : ∀ left right state →
      apply (addOperator left right) state
      ≡ addState (apply left state) (apply right state)

    innerRightAdd : ∀ state left right →
      inner state (addState left right)
      ≡ addBound (inner state left) (inner state right)

    absoluteTriangle : ∀ left right →
      LessEqual
        (absolute (addBound left right))
        (addBound (absolute left) (absolute right))

    selfAdjointAdd : ∀ left right →
      SelfAdjoint left → SelfAdjoint right →
      SelfAdjoint (addOperator left right)

open OperatorFormSumAlgebra public

quadraticFormAbsolute :
  ∀ {Operator State Bound} →
  OperatorFormSumAlgebra Operator State Bound →
  Operator → State → Bound
quadraticFormAbsolute algebra operator state =
  absolute algebra
    (inner algebra state (apply algebra operator state))

formAbsoluteOfSumBelowSum :
  ∀ {Operator State Bound}
    (algebra : OperatorFormSumAlgebra Operator State Bound)
    left right state →
  LessEqual algebra
    (quadraticFormAbsolute algebra
      (addOperator algebra left right) state)
    (addBound algebra
      (quadraticFormAbsolute algebra left state)
      (quadraticFormAbsolute algebra right state))
formAbsoluteOfSumBelowSum algebra left right state =
  subst
    (λ selectedApply → LessEqual algebra
      (absolute algebra
        (inner algebra state selectedApply))
      (addBound algebra
        (quadraticFormAbsolute algebra left state)
        (quadraticFormAbsolute algebra right state)))
    (sym (applyAdd algebra left right state))
    (subst
      (λ selectedInner → LessEqual algebra
        (absolute algebra selectedInner)
        (addBound algebra
          (quadraticFormAbsolute algebra left state)
          (quadraticFormAbsolute algebra right state)))
      (sym (innerRightAdd algebra state
        (apply algebra left state) (apply algebra right state)))
      (absoluteTriangle algebra
        (inner algebra state (apply algebra left state))
        (inner algebra state (apply algebra right state))))

record FiveChannelOperatorSum
    (Operator State Bound : Set) : Set₁ where
  field
    algebra : OperatorFormSumAlgebra Operator State Bound

    total curvature transport chart gauge constraint : Operator

    totalMeaning :
      total ≡ addOperator algebra curvature
        (addOperator algebra transport
          (addOperator algebra chart
            (addOperator algebra gauge constraint)))

    curvatureSelfAdjoint : SelfAdjoint algebra curvature
    transportSelfAdjoint : SelfAdjoint algebra transport
    chartSelfAdjoint : SelfAdjoint algebra chart
    gaugeSelfAdjoint : SelfAdjoint algebra gauge
    constraintSelfAdjoint : SelfAdjoint algebra constraint

open FiveChannelOperatorSum public

nestedFiveChannelSelfAdjoint :
  ∀ {Operator State Bound}
    (dataSet : FiveChannelOperatorSum Operator State Bound) →
  SelfAdjoint (algebra dataSet)
    (addOperator (algebra dataSet) (curvature dataSet)
      (addOperator (algebra dataSet) (transport dataSet)
        (addOperator (algebra dataSet) (chart dataSet)
          (addOperator (algebra dataSet)
            (gauge dataSet) (constraint dataSet)))))
nestedFiveChannelSelfAdjoint dataSet =
  selfAdjointAdd (algebra dataSet)
    (curvature dataSet)
    (addOperator (algebra dataSet) (transport dataSet)
      (addOperator (algebra dataSet) (chart dataSet)
        (addOperator (algebra dataSet)
          (gauge dataSet) (constraint dataSet))))
    (curvatureSelfAdjoint dataSet)
    (selfAdjointAdd (algebra dataSet)
      (transport dataSet)
      (addOperator (algebra dataSet) (chart dataSet)
        (addOperator (algebra dataSet)
          (gauge dataSet) (constraint dataSet)))
      (transportSelfAdjoint dataSet)
      (selfAdjointAdd (algebra dataSet)
        (chart dataSet)
        (addOperator (algebra dataSet)
          (gauge dataSet) (constraint dataSet))
        (chartSelfAdjoint dataSet)
        (selfAdjointAdd (algebra dataSet)
          (gauge dataSet) (constraint dataSet)
          (gaugeSelfAdjoint dataSet)
          (constraintSelfAdjoint dataSet))))

totalFiveChannelSelfAdjoint :
  ∀ {Operator State Bound}
    (dataSet : FiveChannelOperatorSum Operator State Bound) →
  SelfAdjoint (algebra dataSet) (total dataSet)
totalFiveChannelSelfAdjoint dataSet =
  subst
    (SelfAdjoint (algebra dataSet))
    (sym (totalMeaning dataSet))
    (nestedFiveChannelSelfAdjoint dataSet)

nestedFiveChannelFormTriangle :
  ∀ {Operator State Bound}
    (dataSet : FiveChannelOperatorSum Operator State Bound)
    state →
  LessEqual (algebra dataSet)
    (quadraticFormAbsolute (algebra dataSet)
      (addOperator (algebra dataSet) (curvature dataSet)
        (addOperator (algebra dataSet) (transport dataSet)
          (addOperator (algebra dataSet) (chart dataSet)
            (addOperator (algebra dataSet)
              (gauge dataSet) (constraint dataSet))))) state)
    (addBound (algebra dataSet)
      (quadraticFormAbsolute (algebra dataSet)
        (curvature dataSet) state)
      (addBound (algebra dataSet)
        (quadraticFormAbsolute (algebra dataSet)
          (transport dataSet) state)
        (addBound (algebra dataSet)
          (quadraticFormAbsolute (algebra dataSet)
            (chart dataSet) state)
          (addBound (algebra dataSet)
            (quadraticFormAbsolute (algebra dataSet)
              (gauge dataSet) state)
            (quadraticFormAbsolute (algebra dataSet)
              (constraint dataSet) state)))))
nestedFiveChannelFormTriangle dataSet state =
  transitive (algebra dataSet)
    (formAbsoluteOfSumBelowSum (algebra dataSet)
      (curvature dataSet)
      (addOperator (algebra dataSet) (transport dataSet)
        (addOperator (algebra dataSet) (chart dataSet)
          (addOperator (algebra dataSet)
            (gauge dataSet) (constraint dataSet))))
      state)
    (addMonotone (algebra dataSet)
      (reflexive (algebra dataSet)
        (quadraticFormAbsolute (algebra dataSet)
          (curvature dataSet) state))
      (transitive (algebra dataSet)
        (formAbsoluteOfSumBelowSum (algebra dataSet)
          (transport dataSet)
          (addOperator (algebra dataSet) (chart dataSet)
            (addOperator (algebra dataSet)
              (gauge dataSet) (constraint dataSet)))
          state)
        (addMonotone (algebra dataSet)
          (reflexive (algebra dataSet)
            (quadraticFormAbsolute (algebra dataSet)
              (transport dataSet) state))
          (transitive (algebra dataSet)
            (formAbsoluteOfSumBelowSum (algebra dataSet)
              (chart dataSet)
              (addOperator (algebra dataSet)
                (gauge dataSet) (constraint dataSet))
              state)
            (addMonotone (algebra dataSet)
              (reflexive (algebra dataSet)
                (quadraticFormAbsolute (algebra dataSet)
                  (chart dataSet) state))
              (formAbsoluteOfSumBelowSum (algebra dataSet)
                (gauge dataSet) (constraint dataSet) state))))))

totalFiveChannelFormTriangle :
  ∀ {Operator State Bound}
    (dataSet : FiveChannelOperatorSum Operator State Bound)
    state →
  LessEqual (algebra dataSet)
    (quadraticFormAbsolute (algebra dataSet) (total dataSet) state)
    (addBound (algebra dataSet)
      (quadraticFormAbsolute (algebra dataSet)
        (curvature dataSet) state)
      (addBound (algebra dataSet)
        (quadraticFormAbsolute (algebra dataSet)
          (transport dataSet) state)
        (addBound (algebra dataSet)
          (quadraticFormAbsolute (algebra dataSet)
            (chart dataSet) state)
          (addBound (algebra dataSet)
            (quadraticFormAbsolute (algebra dataSet)
              (gauge dataSet) state)
            (quadraticFormAbsolute (algebra dataSet)
              (constraint dataSet) state)))))
totalFiveChannelFormTriangle dataSet state =
  subst
    (λ selectedOperator → LessEqual (algebra dataSet)
      (quadraticFormAbsolute (algebra dataSet)
        selectedOperator state)
      (addBound (algebra dataSet)
        (quadraticFormAbsolute (algebra dataSet)
          (curvature dataSet) state)
        (addBound (algebra dataSet)
          (quadraticFormAbsolute (algebra dataSet)
            (transport dataSet) state)
          (addBound (algebra dataSet)
            (quadraticFormAbsolute (algebra dataSet)
              (chart dataSet) state)
            (addBound (algebra dataSet)
              (quadraticFormAbsolute (algebra dataSet)
                (gauge dataSet) state)
              (quadraticFormAbsolute (algebra dataSet)
                (constraint dataSet) state))))))
    (sym (totalMeaning dataSet))
    (nestedFiveChannelFormTriangle dataSet state)

fiveChannelSumSelfAdjointLevel : ProofLevel
fiveChannelSumSelfAdjointLevel = machineChecked

fiveChannelSumFormTriangleLevel : ProofLevel
fiveChannelSumFormTriangleLevel = machineChecked

physicalFiveChannelOperatorSplitInputsLevel : ProofLevel
physicalFiveChannelOperatorSplitInputsLevel = conditional

physicalChannelSelfAdjointnessInputsLevel : ProofLevel
physicalChannelSelfAdjointnessInputsLevel = conditional

physicalFormLinearityAndTriangleInputsLevel : ProofLevel
physicalFormLinearityAndTriangleInputsLevel = conditional
