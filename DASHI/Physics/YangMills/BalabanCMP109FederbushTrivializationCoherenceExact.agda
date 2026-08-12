module DASHI.Physics.YangMills.BalabanCMP109FederbushTrivializationCoherenceExact where

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
-- DASHI CONTRIBUTION
--
-- Make the left/right trivialization in differentiated equation (0.10)
-- explicit.  With principal-log Jacobian J_j, input tangent u_j and the
-- transport T_j of the centre tangent v into the relative-product chart,
--
--   d log(U_j V^-1) = J_j (u_j - T_j v).
--
-- Finite matrix linearity therefore gives exactly
--
--   w sum_j J_j (u_j - T_j v)
--     = b - Abar v,
--
--   b    = w sum_j J_j u_j,
--   Abar = w sum_j J_j T_j.
--
-- The second theorem records the near-identity telescope
--
--   J(Tv)-v = (J-I)(Tv) + (T-I)v,
--
-- without choosing a norm.  This is the sign/order regression point required
-- before any Federbush inverse estimate is allowed to consume J_j and T_j.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (natAsRational; sumRational)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian

vectorSubtract : Jacobian.Lie3Vector → Jacobian.Lie3Vector → Jacobian.Lie3Vector
vectorSubtract left right coordinate = left coordinate - right coordinate

matrixApplySubtract : ∀ matrix left right coordinate →
  Jacobian.matrixApply matrix (vectorSubtract left right) coordinate
  ≡ Jacobian.matrixApply matrix left coordinate
    - Jacobian.matrixApply matrix right coordinate
matrixApplySubtract matrix left right coordinate =
  finiteSubtract Physical.lieCoordinates3
  where
  finiteSubtract : ∀ values →
    sumRational values
      (λ column → matrix coordinate column * (left column - right column))
    ≡ sumRational values
        (λ column → matrix coordinate column * left column)
      - sumRational values
        (λ column → matrix coordinate column * right column)
  finiteSubtract [] = ℚRing.solve []
  finiteSubtract (column ∷ columns)
    rewrite finiteSubtract columns =
    ℚRing.solve-∀
      (matrix coordinate column) (left column) (right column)
      (sumRational columns
        (λ current → matrix coordinate current * left current))
      (sumRational columns
        (λ current → matrix coordinate current * right current))

record FederbushTrivializationData (Index : Set) : Set₁ where
  field
    indices : List Index
    weight : ℚ
    normalizedWeight : weight * natAsRational (length indices) ≡ 1ℚ

    logJacobian : Index → Jacobian.Lie3Matrix
    centreTransport : Index → Jacobian.Lie3Matrix
    inputTangent : Index → Jacobian.Lie3Vector

open FederbushTrivializationData public

transportedCentreTangent :
  ∀ {Index} → FederbushTrivializationData Index →
  Index → Jacobian.Lie3Vector → Jacobian.Lie3Vector
transportedCentreTangent dataSet index centre =
  Jacobian.matrixApply (centreTransport dataSet index) centre

relativeTangent :
  ∀ {Index} → FederbushTrivializationData Index →
  Index → Jacobian.Lie3Vector → Jacobian.Lie3Vector
relativeTangent dataSet index centre =
  vectorSubtract
    (inputTangent dataSet index)
    (transportedCentreTangent dataSet index centre)

relativeLogDerivative :
  ∀ {Index} → FederbushTrivializationData Index →
  Index → Jacobian.Lie3Vector → Jacobian.Lie3Vector
relativeLogDerivative dataSet index centre =
  Jacobian.matrixApply (logJacobian dataSet index)
    (relativeTangent dataSet index centre)

normalizedInputForcing :
  ∀ {Index} → FederbushTrivializationData Index → Jacobian.Lie3Vector
normalizedInputForcing dataSet coordinate =
  weight dataSet * sumRational (indices dataSet)
    (λ index →
      Jacobian.matrixApply (logJacobian dataSet index)
        (inputTangent dataSet index) coordinate)

normalizedCentreJacobianApply :
  ∀ {Index} → FederbushTrivializationData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector
normalizedCentreJacobianApply dataSet centre coordinate =
  weight dataSet * sumRational (indices dataSet)
    (λ index →
      Jacobian.matrixApply (logJacobian dataSet index)
        (transportedCentreTangent dataSet index centre) coordinate)

normalizedFederbushLinearizedResidual :
  ∀ {Index} → FederbushTrivializationData Index →
  Jacobian.Lie3Vector → Jacobian.Lie3Vector
normalizedFederbushLinearizedResidual dataSet centre coordinate =
  weight dataSet * sumRational (indices dataSet)
    (λ index → relativeLogDerivative dataSet index centre coordinate)

federbushInputDerivativeTrivializationExact :
  ∀ {Index} (dataSet : FederbushTrivializationData Index) centre coordinate →
  normalizedFederbushLinearizedResidual dataSet centre coordinate
  ≡ normalizedInputForcing dataSet coordinate
    - normalizedCentreJacobianApply dataSet centre coordinate
federbushInputDerivativeTrivializationExact dataSet centre coordinate =
  let
    component : ∀ index →
      relativeLogDerivative dataSet index centre coordinate
      ≡ Jacobian.matrixApply (logJacobian dataSet index)
          (inputTangent dataSet index) coordinate
        - Jacobian.matrixApply (logJacobian dataSet index)
          (transportedCentreTangent dataSet index centre) coordinate
    component index =
      matrixApplySubtract
        (logJacobian dataSet index)
        (inputTangent dataSet index)
        (transportedCentreTangent dataSet index centre)
        coordinate
  in
  trans
    (cong (weight dataSet *_)
      (finiteComponentDifference (indices dataSet) component))
    (ℚRing.solve-∀
      (weight dataSet)
      (sumRational (indices dataSet)
        (λ index →
          Jacobian.matrixApply (logJacobian dataSet index)
            (inputTangent dataSet index) coordinate))
      (sumRational (indices dataSet)
        (λ index →
          Jacobian.matrixApply (logJacobian dataSet index)
            (transportedCentreTangent dataSet index centre) coordinate)))
  where
  finiteComponentDifference :
    ∀ values
      (pointwise : ∀ index →
        relativeLogDerivative dataSet index centre coordinate
        ≡ Jacobian.matrixApply (logJacobian dataSet index)
            (inputTangent dataSet index) coordinate
          - Jacobian.matrixApply (logJacobian dataSet index)
            (transportedCentreTangent dataSet index centre) coordinate) →
    sumRational values
      (λ index → relativeLogDerivative dataSet index centre coordinate)
    ≡ sumRational values
        (λ index →
          Jacobian.matrixApply (logJacobian dataSet index)
            (inputTangent dataSet index) coordinate)
      - sumRational values
        (λ index →
          Jacobian.matrixApply (logJacobian dataSet index)
            (transportedCentreTangent dataSet index centre) coordinate)
  finiteComponentDifference [] pointwise = ℚRing.solve []
  finiteComponentDifference (index ∷ rest) pointwise
    rewrite pointwise index | finiteComponentDifference rest pointwise =
    ℚRing.solve-∀
      (Jacobian.matrixApply (logJacobian dataSet index)
        (inputTangent dataSet index) coordinate)
      (Jacobian.matrixApply (logJacobian dataSet index)
        (transportedCentreTangent dataSet index centre) coordinate)
      (sumRational rest
        (λ current →
          Jacobian.matrixApply (logJacobian dataSet current)
            (inputTangent dataSet current) coordinate))
      (sumRational rest
        (λ current →
          Jacobian.matrixApply (logJacobian dataSet current)
            (transportedCentreTangent dataSet current centre) coordinate))

federbushOutputInverseDerivativeTrivializationExact :
  ∀ J T vector coordinate →
  Jacobian.matrixApply J (Jacobian.matrixApply T vector) coordinate
    - vector coordinate
  ≡
  (Jacobian.matrixApply J (Jacobian.matrixApply T vector) coordinate
    - Jacobian.matrixApply T vector coordinate)
  + (Jacobian.matrixApply T vector coordinate - vector coordinate)
federbushOutputInverseDerivativeTrivializationExact J T vector coordinate =
  ℚRing.solve-∀
    (Jacobian.matrixApply J (Jacobian.matrixApply T vector) coordinate)
    (Jacobian.matrixApply T vector coordinate)
    (vector coordinate)

federbushImplicitDerivativeEquationExact :
  ∀ {Index} (dataSet : FederbushTrivializationData Index) centre →
  (∀ coordinate → normalizedFederbushLinearizedResidual dataSet centre coordinate
      ≡ 0ℚ) →
  ∀ coordinate →
  normalizedCentreJacobianApply dataSet centre coordinate
  ≡ normalizedInputForcing dataSet coordinate
federbushImplicitDerivativeEquationExact dataSet centre residualZero coordinate =
  let
    split = federbushInputDerivativeTrivializationExact
      dataSet centre coordinate
    zero = residualZero coordinate
    differenceZero :
      normalizedInputForcing dataSet coordinate
        - normalizedCentreJacobianApply dataSet centre coordinate
      ≡ 0ℚ
    differenceZero = trans (sym split) zero

    translated = cong
      (_+ normalizedCentreJacobianApply dataSet centre coordinate)
      differenceZero

    reduced :
      normalizedInputForcing dataSet coordinate
      ≡ normalizedCentreJacobianApply dataSet centre coordinate
    reduced = trans
      (ℚRing.solve-∀
        (normalizedInputForcing dataSet coordinate)
        (normalizedCentreJacobianApply dataSet centre coordinate))
      (trans translated
        (ℚRing.solve-∀
          (normalizedCentreJacobianApply dataSet centre coordinate)))
  in
  sym reduced

cmp109FederbushInputTrivializationLevel : ProofLevel
cmp109FederbushInputTrivializationLevel = machineChecked

cmp109FederbushOutputInverseTrivializationLevel : ProofLevel
cmp109FederbushOutputInverseTrivializationLevel = machineChecked

cmp109FederbushImplicitLinearEquationLevel : ProofLevel
cmp109FederbushImplicitLinearEquationLevel = machineChecked
