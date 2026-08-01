module DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticChartDefectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- SU(2) Ad/dexp/dexp^-1 defects from one quadratic polynomial theorem.
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
-- On su(2), Cayley--Hamilton reduces every analytic function of ad_X to the
-- span {I, ad_X, ad_X^2}.  Therefore each nonlinear defect appearing in the
-- geometric Hessian channels has the form
--
--   a(X) ad_X + b(X) ad_X^2.
--
-- This module proves the common norm estimate
--
--   ||a ad_X + b ad_X^2||
--     <= |a| A + |b| A^2,       A >= ||ad_X||.
--
-- Ad-I, dexp-I and dexp^-1-I are then three coefficient instantiations of the
-- same theorem.  The physical chart work is reduced to the scalar trigonometric
-- coefficient bounds and one bracket/operator-norm convention.
------------------------------------------------------------------------

record QuadraticOperatorNormAlgebra
    (Operator Scalar : Set) : Set₁ where
  field
    zeroOperator : Operator
    addOperator : Operator → Operator → Operator
    scaleOperator : Scalar → Operator → Operator
    compose : Operator → Operator → Operator

    operatorNorm : Operator → Scalar
    absolute : Scalar → Scalar
    add multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    normTriangle : ∀ left right →
      LessEqual
        (operatorNorm (addOperator left right))
        (add (operatorNorm left) (operatorNorm right))

    normScale : ∀ scalar operator →
      operatorNorm (scaleOperator scalar operator)
      ≡ multiply (absolute scalar) (operatorNorm operator)

    normCompose : ∀ outer inner →
      LessEqual
        (operatorNorm (compose outer inner))
        (multiply (operatorNorm outer) (operatorNorm inner))

open QuadraticOperatorNormAlgebra public

quadraticDefect :
  ∀ {Operator Scalar} →
  QuadraticOperatorNormAlgebra Operator Scalar →
  Operator → Scalar → Scalar → Operator
quadraticDefect algebra adOperator linearCoefficient quadraticCoefficient =
  addOperator algebra
    (scaleOperator algebra linearCoefficient adOperator)
    (scaleOperator algebra quadraticCoefficient
      (compose algebra adOperator adOperator))

quadraticDefectNormBound :
  ∀ {Operator Scalar}
    (algebra : QuadraticOperatorNormAlgebra Operator Scalar)
    adOperator linearCoefficient quadraticCoefficient adBound →
  LessEqual algebra (operatorNorm algebra adOperator) adBound →
  LessEqual algebra
    (operatorNorm algebra
      (quadraticDefect algebra adOperator
        linearCoefficient quadraticCoefficient))
    (add algebra
      (multiply algebra (absolute algebra linearCoefficient) adBound)
      (multiply algebra (absolute algebra quadraticCoefficient)
        (multiply algebra adBound adBound)))
quadraticDefectNormBound algebra adOperator
    linearCoefficient quadraticCoefficient adBound adEstimate =
  transitive algebra
    (normTriangle algebra
      (scaleOperator algebra linearCoefficient adOperator)
      (scaleOperator algebra quadraticCoefficient
        (compose algebra adOperator adOperator)))
    (addMonotone algebra
      (subst
        (λ lower → LessEqual algebra lower
          (multiply algebra
            (absolute algebra linearCoefficient) adBound))
        (sym (normScale algebra linearCoefficient adOperator))
        (multiplyMonotone algebra
          (reflexive algebra (absolute algebra linearCoefficient))
          adEstimate))
      (subst
        (λ lower → LessEqual algebra lower
          (multiply algebra
            (absolute algebra quadraticCoefficient)
            (multiply algebra adBound adBound)))
        (sym
          (normScale algebra quadraticCoefficient
            (compose algebra adOperator adOperator)))
        (multiplyMonotone algebra
          (reflexive algebra (absolute algebra quadraticCoefficient))
          (transitive algebra
            (normCompose algebra adOperator adOperator)
            (multiplyMonotone algebra adEstimate adEstimate))))))

record SU2QuadraticChartDefects
    (Operator Scalar : Set) : Set₁ where
  field
    algebra : QuadraticOperatorNormAlgebra Operator Scalar
    adOperator : Operator
    adBound : Scalar
    adEstimate : LessEqual algebra (operatorNorm algebra adOperator) adBound

    adLinearCoefficient adQuadraticCoefficient : Scalar
    dexpLinearCoefficient dexpQuadraticCoefficient : Scalar
    dexpInverseLinearCoefficient dexpInverseQuadraticCoefficient : Scalar

    adMinusIdentity dexpMinusIdentity dexpInverseMinusIdentity : Operator

    adMinusIdentityMeaning :
      adMinusIdentity
      ≡ quadraticDefect algebra adOperator
          adLinearCoefficient adQuadraticCoefficient

    dexpMinusIdentityMeaning :
      dexpMinusIdentity
      ≡ quadraticDefect algebra adOperator
          dexpLinearCoefficient dexpQuadraticCoefficient

    dexpInverseMinusIdentityMeaning :
      dexpInverseMinusIdentity
      ≡ quadraticDefect algebra adOperator
          dexpInverseLinearCoefficient dexpInverseQuadraticCoefficient

open SU2QuadraticChartDefects public

coefficientBudget :
  ∀ {Operator Scalar} →
  QuadraticOperatorNormAlgebra Operator Scalar →
  Scalar → Scalar → Scalar → Scalar
coefficientBudget algebra linearCoefficient quadraticCoefficient adBound =
  add algebra
    (multiply algebra (absolute algebra linearCoefficient) adBound)
    (multiply algebra (absolute algebra quadraticCoefficient)
      (multiply algebra adBound adBound))

adMinusIdentityBoundFromQuadratic :
  ∀ {Operator Scalar}
    (dataSet : SU2QuadraticChartDefects Operator Scalar) →
  LessEqual (algebra dataSet)
    (operatorNorm (algebra dataSet) (adMinusIdentity dataSet))
    (coefficientBudget (algebra dataSet)
      (adLinearCoefficient dataSet)
      (adQuadraticCoefficient dataSet)
      (adBound dataSet))
adMinusIdentityBoundFromQuadratic dataSet =
  subst
    (λ selected → LessEqual (algebra dataSet)
      (operatorNorm (algebra dataSet) selected)
      (coefficientBudget (algebra dataSet)
        (adLinearCoefficient dataSet)
        (adQuadraticCoefficient dataSet)
        (adBound dataSet)))
    (sym (adMinusIdentityMeaning dataSet))
    (quadraticDefectNormBound (algebra dataSet)
      (adOperator dataSet)
      (adLinearCoefficient dataSet)
      (adQuadraticCoefficient dataSet)
      (adBound dataSet)
      (adEstimate dataSet))

dexpMinusIdentityBoundFromQuadratic :
  ∀ {Operator Scalar}
    (dataSet : SU2QuadraticChartDefects Operator Scalar) →
  LessEqual (algebra dataSet)
    (operatorNorm (algebra dataSet) (dexpMinusIdentity dataSet))
    (coefficientBudget (algebra dataSet)
      (dexpLinearCoefficient dataSet)
      (dexpQuadraticCoefficient dataSet)
      (adBound dataSet))
dexpMinusIdentityBoundFromQuadratic dataSet =
  subst
    (λ selected → LessEqual (algebra dataSet)
      (operatorNorm (algebra dataSet) selected)
      (coefficientBudget (algebra dataSet)
        (dexpLinearCoefficient dataSet)
        (dexpQuadraticCoefficient dataSet)
        (adBound dataSet)))
    (sym (dexpMinusIdentityMeaning dataSet))
    (quadraticDefectNormBound (algebra dataSet)
      (adOperator dataSet)
      (dexpLinearCoefficient dataSet)
      (dexpQuadraticCoefficient dataSet)
      (adBound dataSet)
      (adEstimate dataSet))

dexpInverseMinusIdentityBoundFromQuadratic :
  ∀ {Operator Scalar}
    (dataSet : SU2QuadraticChartDefects Operator Scalar) →
  LessEqual (algebra dataSet)
    (operatorNorm (algebra dataSet) (dexpInverseMinusIdentity dataSet))
    (coefficientBudget (algebra dataSet)
      (dexpInverseLinearCoefficient dataSet)
      (dexpInverseQuadraticCoefficient dataSet)
      (adBound dataSet))
dexpInverseMinusIdentityBoundFromQuadratic dataSet =
  subst
    (λ selected → LessEqual (algebra dataSet)
      (operatorNorm (algebra dataSet) selected)
      (coefficientBudget (algebra dataSet)
        (dexpInverseLinearCoefficient dataSet)
        (dexpInverseQuadraticCoefficient dataSet)
        (adBound dataSet)))
    (sym (dexpInverseMinusIdentityMeaning dataSet))
    (quadraticDefectNormBound (algebra dataSet)
      (adOperator dataSet)
      (dexpInverseLinearCoefficient dataSet)
      (dexpInverseQuadraticCoefficient dataSet)
      (adBound dataSet)
      (adEstimate dataSet))

su2QuadraticDefectNormLevel : ProofLevel
su2QuadraticDefectNormLevel = machineChecked

su2ThreeChartDefectsFromQuadraticLevel : ProofLevel
su2ThreeChartDefectsFromQuadraticLevel = machineChecked

physicalSU2QuadraticCoefficientIdentitiesInputsLevel : ProofLevel
physicalSU2QuadraticCoefficientIdentitiesInputsLevel = conditional

physicalSU2AdjointOperatorNormInputsLevel : ProofLevel
physicalSU2AdjointOperatorNormInputsLevel = conditional
