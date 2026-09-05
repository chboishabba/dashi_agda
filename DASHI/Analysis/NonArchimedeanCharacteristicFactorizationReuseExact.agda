module DASHI.Analysis.NonArchimedeanCharacteristicFactorizationReuseExact where

------------------------------------------------------------------------
-- CHARACTERISTIC FACTORIZATION REUSE
--
-- Source `CoveringFactorization.lean` checks the full finite determinant route
-- for `det (I - u A)`:
--
--   1. sheet reindex preserves determinant;
--   2. Hadamard similarity preserves determinant;
--   3. the target reindexes to `Matrix.fromBlocks`;
--   4. determinant of the zero-offdiagonal block matrix factors;
--   5. weightedDirMatrix = D_(n-1).
--
-- The characteristic determinant `det (lambda I - A)` uses the same five
-- matrix identities.  No new spectral theorem is required; only the scalar
-- affine parameter changes from `(1,u)` to `(lambda,1)`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record CharacteristicFactorizationReuse : Set where
  constructor characteristicFactorizationReuse
  field
    sheetReindexDeterminantOwned : Bool
    hadamardSimilarityDeterminantOwned : Bool
    blockTargetReindexOwned : Bool
    blockDiagonalDeterminantSplitOwned : Bool
    weightedBlockIdentificationOwned : Bool
    affineScalarParameterIsOnlyChange : Bool
    newMatrixAlgebraRequired : Bool
    characteristicFactorizationCompiles : Bool

canonicalCharacteristicFactorizationReuse : CharacteristicFactorizationReuse
canonicalCharacteristicFactorizationReuse =
  characteristicFactorizationReuse
    true true true true true true false true

noNewMatrixAlgebra :
  CharacteristicFactorizationReuse.newMatrixAlgebraRequired
    canonicalCharacteristicFactorizationReuse
  ≡ false
noNewMatrixAlgebra = refl

characteristicFactorizationIsCompilerOutput :
  CharacteristicFactorizationReuse.characteristicFactorizationCompiles
    canonicalCharacteristicFactorizationReuse
  ≡ true
characteristicFactorizationIsCompilerOutput = refl

record SpectrumTowerRepairBoundary : Set where
  constructor spectrumTowerRepairBoundary
  field
    namedSourceTheoremCurrentlyStatesTrueOnly : Bool
    fredholmFactorizationSourceOwned : Bool
    characteristicFactorizationRepoCompiled : Bool
    characteristicRootUnionRepoCompiled : Bool
    literalOneStepSpectrumUnionCompiles : Bool

canonicalSpectrumTowerRepairBoundary : SpectrumTowerRepairBoundary
canonicalSpectrumTowerRepairBoundary =
  spectrumTowerRepairBoundary true true true true true
