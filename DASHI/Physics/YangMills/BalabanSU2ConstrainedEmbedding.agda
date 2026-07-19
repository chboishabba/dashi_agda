module DASHI.Physics.YangMills.BalabanSU2ConstrainedEmbedding where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.BalabanSU2KernelCoordinates using
  (KernelCoordinateDecomposition; Q; coarseEmbedding; kernelEmbedding;
   coarseRightInverse; kernelIsInKernel; combine)

constrainedEmbedding :
  ∀ {Fine Coarse Coordinate} →
  KernelCoordinateDecomposition Fine Coarse Coordinate →
  Coarse → Coordinate → Fine
constrainedEmbedding coordinates coarse coordinate =
  combine coordinates
    (coarseEmbedding coordinates coarse)
    (kernelEmbedding coordinates coordinate)

record ConstraintCompatibleCombination
  {Fine Coarse Coordinate : Set}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) : Set₁ where
  field
    qCombine :
      ∀ coarse coordinate →
      Q coordinates
        (constrainedEmbedding coordinates coarse coordinate)
      ≡ coarse

open ConstraintCompatibleCombination public

constrainedEmbeddingHasAverage :
  ∀ {Fine Coarse Coordinate}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) →
  ConstraintCompatibleCombination coordinates →
  ∀ coarse coordinate →
  Q coordinates (constrainedEmbedding coordinates coarse coordinate) ≡ coarse
constrainedEmbeddingHasAverage coordinates compatibility =
  qCombine compatibility

coarseEmbeddingHasAverage :
  ∀ {Fine Coarse Coordinate}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) →
  ∀ coarse → Q coordinates (coarseEmbedding coordinates coarse) ≡ coarse
coarseEmbeddingHasAverage = coarseRightInverse

kernelEmbeddingHasZeroAverage :
  ∀ {Fine Coarse Coordinate}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) →
  ∀ coordinate →
  Q coordinates (kernelEmbedding coordinates coordinate)
    ≡ DASHI.Physics.YangMills.BalabanSU2KernelCoordinates.coarseZero coordinates
kernelEmbeddingHasZeroAverage = kernelIsInKernel
