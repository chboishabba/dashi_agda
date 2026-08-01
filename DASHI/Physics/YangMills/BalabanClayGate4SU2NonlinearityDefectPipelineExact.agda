module DASHI.Physics.YangMills.BalabanClayGate4SU2NonlinearityDefectPipelineExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One SU(2) nonlinearity defect for curvature, transport and chart.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- The three geometric channels depend on the same local failures of linearity:
--
--   Ad_U - I,    dexp_X - I,    dexp_X^-1 - I.
--
-- This module packages their action norms into one additive defect and derives
-- its uniform unit-state budget from the three operator-norm estimates.  The
-- physical frontier is reduced to proving those three scalar bounds on the
-- selected principal chart.
------------------------------------------------------------------------

record SU2DefectNormAlgebra
    (Operator Vector Bound : Set) : Set₁ where
  field
    apply : Operator → Vector → Vector
    operatorNorm : Operator → Bound
    vectorNorm : Vector → Bound

    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    actionNormBound : ∀ operator vector →
      LessEqual
        (vectorNorm (apply operator vector))
        (multiply (operatorNorm operator) (vectorNorm vector))

open SU2DefectNormAlgebra public

record SU2NonlinearityDefectData
    (Operator Vector Bound : Set) : Set₁ where
  field
    algebra : SU2DefectNormAlgebra Operator Vector Bound

    adDefectOperator dexpDefectOperator dexpInverseDefectOperator : Operator

    adDefectBound dexpDefectBound dexpInverseDefectBound : Bound

    adDefectEstimate :
      LessEqual algebra
        (operatorNorm algebra adDefectOperator)
        adDefectBound

    dexpDefectEstimate :
      LessEqual algebra
        (operatorNorm algebra dexpDefectOperator)
        dexpDefectBound

    dexpInverseDefectEstimate :
      LessEqual algebra
        (operatorNorm algebra dexpInverseDefectOperator)
        dexpInverseDefectBound

    UnitState : Vector → Set
    one : Bound

    unitNormBelowOne : ∀ vector → UnitState vector →
      LessEqual algebra (vectorNorm algebra vector) one

    multiplyRightIdentity : ∀ value →
      multiply algebra value one ≡ value

open SU2NonlinearityDefectData public

componentDefect :
  ∀ {Operator Vector Bound} →
  SU2NonlinearityDefectData Operator Vector Bound →
  Operator → Vector → Bound
componentDefect dataSet operator vector =
  vectorNorm (algebra dataSet)
    (apply (algebra dataSet) operator vector)

componentDefectUniform :
  ∀ {Operator Vector Bound}
    (dataSet : SU2NonlinearityDefectData Operator Vector Bound)
    operator bound vector →
  LessEqual (algebra dataSet)
    (operatorNorm (algebra dataSet) operator) bound →
  UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (componentDefect dataSet operator vector) bound
componentDefectUniform dataSet operator bound vector operatorEstimate unit =
  subst
    (λ upper →
      LessEqual (algebra dataSet)
        (componentDefect dataSet operator vector) upper)
    (multiplyRightIdentity dataSet bound)
    (transitive (algebra dataSet)
      (actionNormBound (algebra dataSet) operator vector)
      (multiplyMonotone (algebra dataSet)
        operatorEstimate
        (unitNormBelowOne dataSet vector unit)))

su2NonlinearityDefect :
  ∀ {Operator Vector Bound} →
  SU2NonlinearityDefectData Operator Vector Bound →
  Vector → Bound
su2NonlinearityDefect dataSet vector =
  add (algebra dataSet)
    (componentDefect dataSet (adDefectOperator dataSet) vector)
    (add (algebra dataSet)
      (componentDefect dataSet (dexpDefectOperator dataSet) vector)
      (componentDefect dataSet (dexpInverseDefectOperator dataSet) vector))

su2NonlinearityBudget :
  ∀ {Operator Vector Bound} →
  SU2NonlinearityDefectData Operator Vector Bound → Bound
su2NonlinearityBudget dataSet =
  add (algebra dataSet)
    (adDefectBound dataSet)
    (add (algebra dataSet)
      (dexpDefectBound dataSet)
      (dexpInverseDefectBound dataSet))

su2NonlinearityDefectUniform :
  ∀ {Operator Vector Bound}
    (dataSet : SU2NonlinearityDefectData Operator Vector Bound)
    vector → UnitState dataSet vector →
  LessEqual (algebra dataSet)
    (su2NonlinearityDefect dataSet vector)
    (su2NonlinearityBudget dataSet)
su2NonlinearityDefectUniform dataSet vector unit =
  addMonotone (algebra dataSet)
    (componentDefectUniform dataSet
      (adDefectOperator dataSet)
      (adDefectBound dataSet)
      vector (adDefectEstimate dataSet) unit)
    (addMonotone (algebra dataSet)
      (componentDefectUniform dataSet
        (dexpDefectOperator dataSet)
        (dexpDefectBound dataSet)
        vector (dexpDefectEstimate dataSet) unit)
      (componentDefectUniform dataSet
        (dexpInverseDefectOperator dataSet)
        (dexpInverseDefectBound dataSet)
        vector (dexpInverseDefectEstimate dataSet) unit))

su2ThreeComponentDefectDefinitionLevel : ProofLevel
su2ThreeComponentDefectDefinitionLevel = computed

su2ThreeComponentUnitDefectLevel : ProofLevel
su2ThreeComponentUnitDefectLevel = machineChecked

physicalAdMinusIdentityNormInputsLevel : ProofLevel
physicalAdMinusIdentityNormInputsLevel = conditional

physicalDexpMinusIdentityNormInputsLevel : ProofLevel
physicalDexpMinusIdentityNormInputsLevel = conditional

physicalDexpInverseMinusIdentityNormInputsLevel : ProofLevel
physicalDexpInverseMinusIdentityNormInputsLevel = conditional
