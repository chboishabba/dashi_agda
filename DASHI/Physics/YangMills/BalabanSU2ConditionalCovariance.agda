module DASHI.Physics.YangMills.BalabanSU2ConditionalCovariance where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  (_∘_; _≈_)
open import DASHI.Physics.YangMills.BalabanConstrainedGaussianCarrierAlgebra using
  (independentCoordinateCovariance; fullConstrainedFluctuationCovariance;
   sourceFullCovarianceFromRestrictedHessian)
open import DASHI.Physics.YangMills.BalabanSU2FiniteHessian using
  (FiniteConstrainedHessian; kernelEmbeddingMap; kernelEmbeddingStar;
   actionHessian; finiteHessian)

record FiniteConditionalCovariance
  {Fine Coordinate Scalar : Set}
  (hessianData : FiniteConstrainedHessian Fine Coordinate Scalar) : Set₁ where
  field
    inverseCoordinate :
      (Coordinate → Coordinate) → Coordinate → Coordinate

    inverseLeft :
      inverseCoordinate (finiteHessian hessianData)
        ∘ finiteHessian hessianData
      ≈ (λ X → X)

    inverseRight :
      finiteHessian hessianData
        ∘ inverseCoordinate (finiteHessian hessianData)
      ≈ (λ X → X)

open FiniteConditionalCovariance public

conditionalCoordinateCovariance :
  ∀ {Fine Coordinate Scalar}
  {hessianData : FiniteConstrainedHessian Fine Coordinate Scalar} →
  FiniteConditionalCovariance hessianData →
  Coordinate → Coordinate
conditionalCoordinateCovariance {hessianData = hessianData} covariance =
  independentCoordinateCovariance
    (inverseCoordinate covariance)
    (kernelEmbeddingMap hessianData)
    (actionHessian hessianData)
    (kernelEmbeddingStar hessianData)

conditionalFullCovariance :
  ∀ {Fine Coordinate Scalar}
  {hessianData : FiniteConstrainedHessian Fine Coordinate Scalar} →
  FiniteConditionalCovariance hessianData →
  Fine → Fine
conditionalFullCovariance {hessianData = hessianData} covariance =
  fullConstrainedFluctuationCovariance
    (kernelEmbeddingMap hessianData)
    (conditionalCoordinateCovariance covariance)
    (kernelEmbeddingStar hessianData)

conditionalCoordinateCovarianceLeftInverse :
  ∀ {Fine Coordinate Scalar}
  {hessianData : FiniteConstrainedHessian Fine Coordinate Scalar}
  (covariance : FiniteConditionalCovariance hessianData) →
  conditionalCoordinateCovariance covariance
    ∘ finiteHessian hessianData
  ≈ (λ X → X)
conditionalCoordinateCovarianceLeftInverse = inverseLeft

conditionalCoordinateCovarianceRightInverse :
  ∀ {Fine Coordinate Scalar}
  {hessianData : FiniteConstrainedHessian Fine Coordinate Scalar}
  (covariance : FiniteConditionalCovariance hessianData) →
  finiteHessian hessianData
    ∘ conditionalCoordinateCovariance covariance
  ≈ (λ X → X)
conditionalCoordinateCovarianceRightInverse = inverseRight

conditionalFullCovarianceFormula :
  ∀ {Fine Coordinate Scalar}
  {hessianData : FiniteConstrainedHessian Fine Coordinate Scalar}
  (covariance : FiniteConditionalCovariance hessianData) →
  conditionalFullCovariance covariance
  ≡ kernelEmbeddingMap hessianData
      ∘ inverseCoordinate covariance (finiteHessian hessianData)
      ∘ kernelEmbeddingStar hessianData
conditionalFullCovarianceFormula {hessianData = hessianData} covariance =
  sourceFullCovarianceFromRestrictedHessian
    (inverseCoordinate covariance)
    (kernelEmbeddingMap hessianData)
    (actionHessian hessianData)
    (kernelEmbeddingStar hessianData)
