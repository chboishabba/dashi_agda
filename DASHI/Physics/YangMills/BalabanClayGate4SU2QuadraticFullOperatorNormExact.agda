module DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticFullOperatorNormExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticChartDefectExact as Quadratic
import DASHI.Physics.YangMills.BalabanClayGate4IdentityDefectOperatorNormExact as IdentityDefect

------------------------------------------------------------------------
-- Full dexp and dexp^-1 bounds from the SU(2) quadratic defects.
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
-- Once the quadratic chart module proves bounds for dexp-I and dexp^-1-I,
-- the complete stage constants used by the CMP109 derivative pipeline are
--
--   M_exp <= 1 + delta_exp,
--   M_log <= 1 + delta_log.
------------------------------------------------------------------------

record SU2QuadraticFullOperatorInputs
    (Operator Bound : Set) : Set₁ where
  field
    quadratic : Quadratic.SU2QuadraticChartDefects Operator Bound
    identityAlgebra : IdentityDefect.IdentityDefectNormAlgebra Operator Bound

    operatorNormMeaning : ∀ operator →
      IdentityDefect.operatorNorm identityAlgebra operator
      ≡ Quadratic.operatorNorm (Quadratic.algebra quadratic) operator

    orderMeaning :
      IdentityDefect.LessEqual identityAlgebra
      ≡ Quadratic.LessEqual (Quadratic.algebra quadratic)

    dexp dexpInverse : Operator

    dexpMeaning :
      dexp
      ≡ IdentityDefect.addOperator identityAlgebra
          (IdentityDefect.identityOperator identityAlgebra)
          (Quadratic.dexpMinusIdentity quadratic)

    dexpInverseMeaning :
      dexpInverse
      ≡ IdentityDefect.addOperator identityAlgebra
          (IdentityDefect.identityOperator identityAlgebra)
          (Quadratic.dexpInverseMinusIdentity quadratic)

open SU2QuadraticFullOperatorInputs public

transportQuadraticDefectEstimate :
  ∀ {Operator Bound}
    (inputs : SU2QuadraticFullOperatorInputs Operator Bound)
    operator bound →
  Quadratic.LessEqual (Quadratic.algebra (quadratic inputs))
    (Quadratic.operatorNorm (Quadratic.algebra (quadratic inputs)) operator)
    bound →
  IdentityDefect.LessEqual (identityAlgebra inputs)
    (IdentityDefect.operatorNorm (identityAlgebra inputs) operator)
    bound
transportQuadraticDefectEstimate inputs operator bound estimate =
  subst
    (λ lower →
      IdentityDefect.LessEqual (identityAlgebra inputs) lower bound)
    (sym (operatorNormMeaning inputs operator))
    (subst
      (λ relation → relation
        (Quadratic.operatorNorm
          (Quadratic.algebra (quadratic inputs)) operator)
        bound)
      (sym (orderMeaning inputs))
      estimate)

dexpDefectData :
  ∀ {Operator Bound} →
  SU2QuadraticFullOperatorInputs Operator Bound →
  IdentityDefect.OperatorFromIdentityDefect Operator Bound
dexpDefectData inputs = record
  { IdentityDefect.OperatorFromIdentityDefect.algebra = identityAlgebra inputs
  ; IdentityDefect.OperatorFromIdentityDefect.operator = dexp inputs
  ; IdentityDefect.OperatorFromIdentityDefect.defect =
      Quadratic.dexpMinusIdentity (quadratic inputs)
  ; IdentityDefect.OperatorFromIdentityDefect.defectBound =
      Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.dexpLinearCoefficient (quadratic inputs))
        (Quadratic.dexpQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))
  ; IdentityDefect.OperatorFromIdentityDefect.operatorMeaning =
      dexpMeaning inputs
  ; IdentityDefect.OperatorFromIdentityDefect.defectEstimate =
      transportQuadraticDefectEstimate inputs
        (Quadratic.dexpMinusIdentity (quadratic inputs))
        (Quadratic.coefficientBudget
          (Quadratic.algebra (quadratic inputs))
          (Quadratic.dexpLinearCoefficient (quadratic inputs))
          (Quadratic.dexpQuadraticCoefficient (quadratic inputs))
          (Quadratic.adBound (quadratic inputs)))
        (Quadratic.dexpMinusIdentityBoundFromQuadratic
          (quadratic inputs))
  }

dexpInverseDefectData :
  ∀ {Operator Bound} →
  SU2QuadraticFullOperatorInputs Operator Bound →
  IdentityDefect.OperatorFromIdentityDefect Operator Bound
dexpInverseDefectData inputs = record
  { IdentityDefect.OperatorFromIdentityDefect.algebra = identityAlgebra inputs
  ; IdentityDefect.OperatorFromIdentityDefect.operator = dexpInverse inputs
  ; IdentityDefect.OperatorFromIdentityDefect.defect =
      Quadratic.dexpInverseMinusIdentity (quadratic inputs)
  ; IdentityDefect.OperatorFromIdentityDefect.defectBound =
      Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.dexpInverseLinearCoefficient (quadratic inputs))
        (Quadratic.dexpInverseQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))
  ; IdentityDefect.OperatorFromIdentityDefect.operatorMeaning =
      dexpInverseMeaning inputs
  ; IdentityDefect.OperatorFromIdentityDefect.defectEstimate =
      transportQuadraticDefectEstimate inputs
        (Quadratic.dexpInverseMinusIdentity (quadratic inputs))
        (Quadratic.coefficientBudget
          (Quadratic.algebra (quadratic inputs))
          (Quadratic.dexpInverseLinearCoefficient (quadratic inputs))
          (Quadratic.dexpInverseQuadraticCoefficient (quadratic inputs))
          (Quadratic.adBound (quadratic inputs)))
        (Quadratic.dexpInverseMinusIdentityBoundFromQuadratic
          (quadratic inputs))
  }

dexpNormFromQuadraticDefect :
  ∀ {Operator Bound}
    (inputs : SU2QuadraticFullOperatorInputs Operator Bound) →
  IdentityDefect.LessEqual (identityAlgebra inputs)
    (IdentityDefect.operatorNorm (identityAlgebra inputs) (dexp inputs))
    (IdentityDefect.addBound (identityAlgebra inputs)
      (IdentityDefect.one (identityAlgebra inputs))
      (Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.dexpLinearCoefficient (quadratic inputs))
        (Quadratic.dexpQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))))
dexpNormFromQuadraticDefect inputs =
  IdentityDefect.operatorNormBelowOnePlusDefect (dexpDefectData inputs)

dexpInverseNormFromQuadraticDefect :
  ∀ {Operator Bound}
    (inputs : SU2QuadraticFullOperatorInputs Operator Bound) →
  IdentityDefect.LessEqual (identityAlgebra inputs)
    (IdentityDefect.operatorNorm (identityAlgebra inputs)
      (dexpInverse inputs))
    (IdentityDefect.addBound (identityAlgebra inputs)
      (IdentityDefect.one (identityAlgebra inputs))
      (Quadratic.coefficientBudget
        (Quadratic.algebra (quadratic inputs))
        (Quadratic.dexpInverseLinearCoefficient (quadratic inputs))
        (Quadratic.dexpInverseQuadraticCoefficient (quadratic inputs))
        (Quadratic.adBound (quadratic inputs))))
dexpInverseNormFromQuadraticDefect inputs =
  IdentityDefect.operatorNormBelowOnePlusDefect
    (dexpInverseDefectData inputs)

su2DexpFullNormFromQuadraticLevel : ProofLevel
su2DexpFullNormFromQuadraticLevel = machineChecked

su2DexpInverseFullNormFromQuadraticLevel : ProofLevel
su2DexpInverseFullNormFromQuadraticLevel = machineChecked

physicalSU2FullOperatorIdentityInputsLevel : ProofLevel
physicalSU2FullOperatorIdentityInputsLevel = conditional
