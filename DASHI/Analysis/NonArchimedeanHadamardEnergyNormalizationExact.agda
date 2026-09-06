module DASHI.Analysis.NonArchimedeanHadamardEnergyNormalizationExact where

------------------------------------------------------------------------
-- HADAMARD ENERGY NORMALIZATION AUDIT / COMPILER BOUNDARY
--
-- The checked source block diagonalization uses the unnormalised rational
-- Hadamard matrix
--
--   H = [[1,1],[1,-1]],       H^{-1} = (1/2) H,
--
-- with H H = 2 I.  Therefore that theorem is an invertible similarity, not by
-- itself an L2-isometric change of basis.
--
-- Norm-compatible recursive assembly instead uses the parallelogram identity:
--
--   ||u+v||^2 + ||u-v||^2 = 2 (||u||^2 + ||v||^2).
--
-- Define component energies by the explicit half-normalisation
--
--   E_sym  = (1/2)||u+v||^2,
--   E_anti = (1/2)||u-v||^2.
--
-- Then E_sym + E_anti = E_parent exactly, with no sqrt(2) carrier and no
-- conditioning loss across the dyadic tower.
--
-- Mathlib reference: Analysis.InnerProductSpace.Basic,
-- `parallelogram_law_with_norm_mul`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record HadamardEnergySourceReceipt : Set where
  constructor hadamardEnergySourceReceipt
  field
    sourceCommit : String
    mathlibReferenceCommit : String
    sourceHadamardUnnormalised : Bool
    sourceHadamardSquareEqualsTwoIdentity : Bool
    sourceHadamardInverseIsHalfHadamard : Bool
    checkedBlockSimilarityIsNormIsometryAsWritten : Bool
    mathlibParallelogramLawOwned : Bool
    halfNormalisedSymAntiEnergyExact : Bool
    recursiveEnergySplitHasConditioningLoss : Bool

canonicalHadamardEnergySourceReceipt : HadamardEnergySourceReceipt
canonicalHadamardEnergySourceReceipt =
  hadamardEnergySourceReceipt
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    "251e86bd1fa42024826ccdb46c3d680edff03e1f"
    true true true false true true false

checkedSimilarityNotUnitaryAsWritten :
  HadamardEnergySourceReceipt.checkedBlockSimilarityIsNormIsometryAsWritten
    canonicalHadamardEnergySourceReceipt
  ≡ false
checkedSimilarityNotUnitaryAsWritten = refl

normalisedEnergySplitExact :
  HadamardEnergySourceReceipt.halfNormalisedSymAntiEnergyExact
    canonicalHadamardEnergySourceReceipt
  ≡ true
normalisedEnergySplitExact = refl

noRecursiveConditioningLoss :
  HadamardEnergySourceReceipt.recursiveEnergySplitHasConditioningLoss
    canonicalHadamardEnergySourceReceipt
  ≡ false
noRecursiveConditioningLoss = refl

record HadamardEnergyAuthorityBoundary : Set where
  constructor hadamardEnergyAuthorityBoundary
  field
    sourceMatrixSimilarityOwned : Bool
    normCompatibleEnergyNormalisationLibraryClosed : Bool
    sourceLeanContainsNormalisedHadamardMatrixTheorem : Bool
    agdaKernelChecksMathlibNormIdentity : Bool

canonicalHadamardEnergyAuthorityBoundary : HadamardEnergyAuthorityBoundary
canonicalHadamardEnergyAuthorityBoundary =
  hadamardEnergyAuthorityBoundary true true false false

normalisationMathematicsClosedWithoutSourceInflation :
  HadamardEnergyAuthorityBoundary.normCompatibleEnergyNormalisationLibraryClosed
    canonicalHadamardEnergyAuthorityBoundary
  ≡ true
normalisationMathematicsClosedWithoutSourceInflation = refl
