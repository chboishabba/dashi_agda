module DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticNonlinearityAdapterExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticChartDefectExact as Quadratic
import DASHI.Physics.YangMills.BalabanClayGate4SU2NonlinearityDefectPipelineExact as Defect

------------------------------------------------------------------------
-- Common SU(2) defect with all three operator estimates derived.
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
-- The quadratic su(2) chart theorem derives the three operator bounds.  This
-- adapter transports them to the vector-action norm used by the five-channel
-- majorant and constructs the common nonlinearity defect.  Consequently the
-- physical consumer no longer supplies separate Ad-I, dexp-I and dexp^-1-I
-- norm estimates.
------------------------------------------------------------------------

record SU2QuadraticNonlinearityInputs
    (Operator Vector Bound : Set) : Set₁ where
  field
    quadratic : Quadratic.SU2QuadraticChartDefects Operator Bound
    vectorAlgebra : Defect.SU2DefectNormAlgebra Operator Vector Bound

    operatorNormMeaning : ∀ operator →
      Defect.operatorNorm vectorAlgebra operator
      ≡ Quadratic.operatorNorm (Quadratic.algebra quadratic) operator

    orderMeaning :
      Defect.LessEqual vectorAlgebra
      ≡ Quadratic.LessEqual (Quadratic.algebra quadratic)

    UnitState : Vector → Set
    one : Bound

    unitNormBelowOne : ∀ vector → UnitState vector →
      Defect.LessEqual vectorAlgebra
        (Defect.vectorNorm vectorAlgebra vector) one

    multiplyRightIdentity : ∀ value →
      Defect.multiply vectorAlgebra value one ≡ value

open SU2QuadraticNonlinearityInputs public

transportQuadraticOperatorEstimate :
  ∀ {Operator Vector Bound}
    (inputs : SU2QuadraticNonlinearityInputs Operator Vector Bound)
    operator bound →
  Quadratic.LessEqual (Quadratic.algebra (quadratic inputs))
    (Quadratic.operatorNorm (Quadratic.algebra (quadratic inputs)) operator)
    bound →
  Defect.LessEqual (vectorAlgebra inputs)
    (Defect.operatorNorm (vectorAlgebra inputs) operator)
    bound
transportQuadraticOperatorEstimate inputs operator bound estimate =
  subst
    (λ lower → Defect.LessEqual (vectorAlgebra inputs) lower bound)
    (sym (operatorNormMeaning inputs operator))
    (subst
      (λ relation → relation
        (Quadratic.operatorNorm
          (Quadratic.algebra (quadratic inputs)) operator)
        bound)
      (sym (orderMeaning inputs))
      estimate)

asSU2NonlinearityDefectData :
  ∀ {Operator Vector Bound} →
  SU2QuadraticNonlinearityInputs Operator Vector Bound →
  Defect.SU2NonlinearityDefectData Operator Vector Bound
asSU2NonlinearityDefectData inputs = record
  { Defect.SU2NonlinearityDefectData.algebra = vectorAlgebra inputs
  ; Defect.SU2NonlinearityDefectData.adDefectOperator =
      Quadratic.adMinusIdentity (quadratic inputs)
  ; Defect.SU2NonlinearityDefectData.dexpDefectOperator =
      Quadratic.dexpMinusIdentity (quadratic inputs)
  ; Defect.SU2NonlinearityDefectData.dexpInverseDefectOperator =
      Quadratic.dexpInverseMinusIdentity (quadratic inputs)
  ; Defect.SU2NonlinearityDefectData.adDefectBound =
      Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.adLinearCoefficient (quadratic inputs))
        (Quadratic.adQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))
  ; Defect.SU2NonlinearityDefectData.dexpDefectBound =
      Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.dexpLinearCoefficient (quadratic inputs))
        (Quadratic.dexpQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))
  ; Defect.SU2NonlinearityDefectData.dexpInverseDefectBound =
      Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.dexpInverseLinearCoefficient (quadratic inputs))
        (Quadratic.dexpInverseQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))
  ; Defect.SU2NonlinearityDefectData.adDefectEstimate =
      transportQuadraticOperatorEstimate inputs
        (Quadratic.adMinusIdentity (quadratic inputs))
        (Quadratic.coefficientBudget
          (Quadratic.algebra (quadratic inputs))
          (Quadratic.adLinearCoefficient (quadratic inputs))
          (Quadratic.adQuadraticCoefficient (quadratic inputs))
          (Quadratic.adBound (quadratic inputs)))
        (Quadratic.adMinusIdentityBoundFromQuadratic (quadratic inputs))
  ; Defect.SU2NonlinearityDefectData.dexpDefectEstimate =
      transportQuadraticOperatorEstimate inputs
        (Quadratic.dexpMinusIdentity (quadratic inputs))
        (Quadratic.coefficientBudget
          (Quadratic.algebra (quadratic inputs))
          (Quadratic.dexpLinearCoefficient (quadratic inputs))
          (Quadratic.dexpQuadraticCoefficient (quadratic inputs))
          (Quadratic.adBound (quadratic inputs)))
        (Quadratic.dexpMinusIdentityBoundFromQuadratic (quadratic inputs))
  ; Defect.SU2NonlinearityDefectData.dexpInverseDefectEstimate =
      transportQuadraticOperatorEstimate inputs
        (Quadratic.dexpInverseMinusIdentity (quadratic inputs))
        (Quadratic.coefficientBudget
          (Quadratic.algebra (quadratic inputs))
          (Quadratic.dexpInverseLinearCoefficient (quadratic inputs))
          (Quadratic.dexpInverseQuadraticCoefficient (quadratic inputs))
          (Quadratic.adBound (quadratic inputs)))
        (Quadratic.dexpInverseMinusIdentityBoundFromQuadratic
          (quadratic inputs))
  ; Defect.SU2NonlinearityDefectData.UnitState = UnitState inputs
  ; Defect.SU2NonlinearityDefectData.one = one inputs
  ; Defect.SU2NonlinearityDefectData.unitNormBelowOne =
      unitNormBelowOne inputs
  ; Defect.SU2NonlinearityDefectData.multiplyRightIdentity =
      multiplyRightIdentity inputs
  }

su2QuadraticToCommonDefectLevel : ProofLevel
su2QuadraticToCommonDefectLevel = machineChecked

su2QuadraticCommonDefectUniformityLevel : ProofLevel
su2QuadraticCommonDefectUniformityLevel = machineChecked

physicalSU2QuadraticVectorNormBridgeInputsLevel : ProofLevel
physicalSU2QuadraticVectorNormBridgeInputsLevel = conditional
