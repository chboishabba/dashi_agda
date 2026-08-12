module DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushDifferentiatedEquation011Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Make the equation-(0.11) same-object seam proof relevant.  For each literal
-- contour contribution the printed differentiated input leg and centre leg are
-- identified with the *same* principal-log Jacobian J_j and the *same* centre
-- transport T_j:
--
--   D_U log(U_j V^-1)[u_j] = J_j u_j,
--   D_V log(U_j V^-1)[v]   = - J_j T_j v.
--
-- Summing the actual printed component derivatives therefore gives exactly
--
--   sum_j J_j u_j - sum_j J_j T_j v.
--
-- Hence a zero derivative of the printed Federbush equation is literally the
-- finite matrix equation
--
--   (sum_j J_j T_j) v = sum_j J_j u_j.
--
-- This module deliberately does not accept independently supplied aggregate
-- matrices: both sides are constructed from the component J_j/T_j witnesses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualExact as Component
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1

sumIndex : ∀ {Index : Set} → List Index → (Index → ℚ) → ℚ
sumIndex [] value = 0ℚ
sumIndex (index ∷ indices) value = value index + sumIndex indices value

sumIndexCong :
  ∀ {Index : Set} (indices : List Index) left right →
  (∀ index → left index ≡ right index) →
  sumIndex indices left ≡ sumIndex indices right
sumIndexCong [] left right pointwise = ℚRing.solve []
sumIndexCong (index ∷ indices) left right pointwise =
  trans
    (cong (left index +_) (sumIndexCong indices left right pointwise))
    (cong (_+ sumIndex indices right) (pointwise index))

sumIndexDifference :
  ∀ {Index : Set} (indices : List Index) left right →
  sumIndex indices (λ index → left index - right index)
  ≡ sumIndex indices left - sumIndex indices right
sumIndexDifference [] left right = ℚRing.solve []
sumIndexDifference (index ∷ indices) left right
  rewrite sumIndexDifference indices left right =
  ℚRing.solve-∀
    (left index) (right index)
    (sumIndex indices left) (sumIndex indices right)

applyMatrix : Jacobian.Lie3Matrix → Jacobian.Lie3Vector → Jacobian.Lie3Vector
applyMatrix matrix vector =
  L1.applyKernel Physical.lieCoordinates3 matrix vector

composeMatrix : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
composeMatrix = Component.matrixCompose

record PhysicalFederbushEquation011Differential (Index : Set) : Set₁ where
  field
    indices : List Index

    principalLogJacobian : Index → Jacobian.Lie3Matrix
    centreTransport : Index → Jacobian.Lie3Matrix
    inputVariation : Index → Jacobian.Lie3Vector
    averageVariation : Jacobian.Lie3Vector

    -- Literal derivatives of the printed contour term.  These fields are the
    -- semantic objects obtained by differentiating log(U_j V^-1), not generic
    -- replacement kernels.
    printedInputDerivative : Index → Jacobian.Lie3Vector
    printedCentreDerivative : Index → Jacobian.Lie3Vector

    printedInputDerivativeExact : ∀ index row →
      printedInputDerivative index row
      ≡ applyMatrix (principalLogJacobian index) (inputVariation index) row

    printedCentreDerivativeExact : ∀ index row →
      printedCentreDerivative index row
      ≡ 0ℚ - applyMatrix
          (composeMatrix (principalLogJacobian index) (centreTransport index))
          averageVariation row

open PhysicalFederbushEquation011Differential public

printedComponentDerivative :
  ∀ {Index} → PhysicalFederbushEquation011Differential Index →
  Index → Jacobian.Lie3Vector
printedComponentDerivative dataSet index row =
  printedInputDerivative dataSet index row
    + printedCentreDerivative dataSet index row

inputAggregate :
  ∀ {Index} → PhysicalFederbushEquation011Differential Index →
  Jacobian.Lie3Vector
inputAggregate dataSet row =
  sumIndex (indices dataSet)
    (λ index →
      applyMatrix
        (principalLogJacobian dataSet index)
        (inputVariation dataSet index) row)

centreAggregate :
  ∀ {Index} → PhysicalFederbushEquation011Differential Index →
  Jacobian.Lie3Vector
centreAggregate dataSet row =
  sumIndex (indices dataSet)
    (λ index →
      applyMatrix
        (composeMatrix
          (principalLogJacobian dataSet index)
          (centreTransport dataSet index))
        (averageVariation dataSet) row)

printedEquation011Derivative :
  ∀ {Index} → PhysicalFederbushEquation011Differential Index →
  Jacobian.Lie3Vector
printedEquation011Derivative dataSet row =
  sumIndex (indices dataSet)
    (λ index → printedComponentDerivative dataSet index row)

printedComponentDerivativeExact :
  ∀ {Index} (dataSet : PhysicalFederbushEquation011Differential Index)
    index row →
  printedComponentDerivative dataSet index row
  ≡ applyMatrix
      (principalLogJacobian dataSet index)
      (inputVariation dataSet index) row
    - applyMatrix
      (composeMatrix
        (principalLogJacobian dataSet index)
        (centreTransport dataSet index))
      (averageVariation dataSet) row
printedComponentDerivativeExact dataSet index row =
  trans
    (cong
      (printedInputDerivative dataSet index row +_)
      (printedCentreDerivativeExact dataSet index row))
    (trans
      (cong
        (λ left →
          left
          + (0ℚ - applyMatrix
              (composeMatrix
                (principalLogJacobian dataSet index)
                (centreTransport dataSet index))
              (averageVariation dataSet) row))
        (printedInputDerivativeExact dataSet index row))
      (ℚRing.solve-∀
        (applyMatrix
          (principalLogJacobian dataSet index)
          (inputVariation dataSet index) row)
        (applyMatrix
          (composeMatrix
            (principalLogJacobian dataSet index)
            (centreTransport dataSet index))
          (averageVariation dataSet) row)))

printedEquation011CollectedExact :
  ∀ {Index} (dataSet : PhysicalFederbushEquation011Differential Index) row →
  printedEquation011Derivative dataSet row
  ≡ inputAggregate dataSet row - centreAggregate dataSet row
printedEquation011CollectedExact dataSet row =
  trans
    (sumIndexCong
      (indices dataSet)
      (λ index → printedComponentDerivative dataSet index row)
      (λ index →
        applyMatrix
          (principalLogJacobian dataSet index)
          (inputVariation dataSet index) row
        - applyMatrix
          (composeMatrix
            (principalLogJacobian dataSet index)
            (centreTransport dataSet index))
          (averageVariation dataSet) row)
      (λ index → printedComponentDerivativeExact dataSet index row))
    (sumIndexDifference
      (indices dataSet)
      (λ index →
        applyMatrix
          (principalLogJacobian dataSet index)
          (inputVariation dataSet index) row)
      (λ index →
        applyMatrix
          (composeMatrix
            (principalLogJacobian dataSet index)
            (centreTransport dataSet index))
          (averageVariation dataSet) row))

differenceZeroImpliesRightEqualsLeft : ∀ left right →
  left - right ≡ 0ℚ → right ≡ left
differenceZeroImpliesRightEqualsLeft left right differenceZero =
  trans
    (ℚRing.solve-∀ left right)
    (trans
      (cong (right +_) differenceZero)
      (ℚRing.solve-∀ left right))

physicalFederbushDifferentiatedEquation011Exact :
  ∀ {Index} (dataSet : PhysicalFederbushEquation011Differential Index) →
  (∀ row → printedEquation011Derivative dataSet row ≡ 0ℚ) →
  ∀ row → centreAggregate dataSet row ≡ inputAggregate dataSet row
physicalFederbushDifferentiatedEquation011Exact dataSet printedZero row =
  differenceZeroImpliesRightEqualsLeft
    (inputAggregate dataSet row)
    (centreAggregate dataSet row)
    (trans
      (sym (printedEquation011CollectedExact dataSet row))
      (printedZero row))

cmp109PhysicalFederbushComponentDifferentialLevel : ProofLevel
cmp109PhysicalFederbushComponentDifferentialLevel = machineChecked

cmp109PhysicalFederbushDifferentiatedEquation011Level : ProofLevel
cmp109PhysicalFederbushDifferentiatedEquation011Level = machineChecked
