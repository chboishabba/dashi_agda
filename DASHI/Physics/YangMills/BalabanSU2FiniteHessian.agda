module DASHI.Physics.YangMills.BalabanSU2FiniteHessian where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.BalabanConstrainedGaussianCarrierAlgebra using
  (restrictedCoordinateHessian)
open import DASHI.Physics.YangMills.BalabanSU2KernelCoordinates using
  (KernelCoordinateDecomposition; kernelEmbedding)

record FiniteConstrainedHessian
  (Fine Coordinate Scalar : Set) : Set₁ where
  field
    actionHessian : Fine → Fine
    kernelEmbeddingStar : Fine → Coordinate
    kernelEmbeddingMap : Coordinate → Fine

    scalarZero : Scalar
    scalarOrder : Scalar → Scalar → Set
    coordinateInner : Coordinate → Coordinate → Scalar

    restrictedSymmetric :
      ∀ X Y →
      coordinateInner X
        (restrictedCoordinateHessian
          kernelEmbeddingMap actionHessian kernelEmbeddingStar Y)
      ≡
      coordinateInner
        (restrictedCoordinateHessian
          kernelEmbeddingMap actionHessian kernelEmbeddingStar X)
        Y

    coercivityConstant : Scalar
    coerciveOnKernelCoordinates :
      ∀ X →
      scalarOrder
        (coordinateInner X
          (restrictedCoordinateHessian
            kernelEmbeddingMap actionHessian kernelEmbeddingStar X))
        (coordinateInner X X)

open FiniteConstrainedHessian public

finiteHessian :
  ∀ {Fine Coordinate Scalar} →
  FiniteConstrainedHessian Fine Coordinate Scalar →
  Coordinate → Coordinate
finiteHessian h =
  restrictedCoordinateHessian
    (kernelEmbeddingMap h)
    (actionHessian h)
    (kernelEmbeddingStar h)

finiteHessianSymmetric :
  ∀ {Fine Coordinate Scalar}
  (h : FiniteConstrainedHessian Fine Coordinate Scalar) →
  ∀ X Y →
  coordinateInner h X (finiteHessian h Y)
    ≡ coordinateInner h (finiteHessian h X) Y
finiteHessianSymmetric = restrictedSymmetric

finiteHessianCoercive :
  ∀ {Fine Coordinate Scalar}
  (h : FiniteConstrainedHessian Fine Coordinate Scalar) →
  ∀ X →
  scalarOrder h
    (coordinateInner h X (finiteHessian h X))
    (coordinateInner h X X)
finiteHessianCoercive = coerciveOnKernelCoordinates
