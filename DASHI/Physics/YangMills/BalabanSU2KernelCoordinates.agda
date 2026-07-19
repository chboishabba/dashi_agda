module DASHI.Physics.YangMills.BalabanSU2KernelCoordinates where

open import Agda.Builtin.Equality using (_≡_)

-- A finite coordinate realization is kept fully constructive: it contains the
-- two embeddings and the projections together with the exact reconstruction
-- equations.  No choice principle or hidden inverse is used.
record KernelCoordinateDecomposition
  (Fine Coarse Coordinate : Set) : Set₁ where
  field
    coarseZero : Coarse
    coordinateZero : Coordinate

    Q : Fine → Coarse
    coarseEmbedding : Coarse → Fine
    kernelEmbedding : Coordinate → Fine

    coarseProjection : Fine → Coarse
    kernelProjection : Fine → Coordinate
    combine : Fine → Fine → Fine

    coarseRightInverse :
      ∀ coarse → Q (coarseEmbedding coarse) ≡ coarse

    kernelIsInKernel :
      ∀ coordinate → Q (kernelEmbedding coordinate) ≡ coarseZero

    coarseProjectionCorrect :
      ∀ fine → coarseProjection fine ≡ Q fine

    reconstruction :
      ∀ fine →
      combine
        (coarseEmbedding (coarseProjection fine))
        (kernelEmbedding (kernelProjection fine))
      ≡ fine

    kernelProjectionEmbedding :
      ∀ coordinate →
      kernelProjection (kernelEmbedding coordinate) ≡ coordinate

open KernelCoordinateDecomposition public

C-kerQ :
  ∀ {Fine Coarse Coordinate}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) →
  Coordinate → Fine
C-kerQ = kernelEmbedding

Q-C-kerQ-zero :
  ∀ {Fine Coarse Coordinate}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) →
  ∀ coordinate →
  Q coordinates (C-kerQ coordinates coordinate) ≡ coarseZero coordinates
Q-C-kerQ-zero = kernelIsInKernel

fineCoordinateDecomposition :
  ∀ {Fine Coarse Coordinate}
  (coordinates : KernelCoordinateDecomposition Fine Coarse Coordinate) →
  ∀ fine →
  combine coordinates
    (coarseEmbedding coordinates (Q coordinates fine))
    (kernelEmbedding coordinates (kernelProjection coordinates fine))
  ≡ fine
fineCoordinateDecomposition coordinates fine
  rewrite coarseProjectionCorrect coordinates fine =
  reconstruction coordinates fine
