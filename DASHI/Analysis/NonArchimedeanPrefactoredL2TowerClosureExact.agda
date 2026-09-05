module DASHI.Analysis.NonArchimedeanPrefactoredL2TowerClosureExact where

------------------------------------------------------------------------
-- PREFACTORED L2 TOWER CLOSURE
--
-- Correct whole-level route after the exact n=3 refutation of the source's
-- unit-prefactor one-step inverse-sqrt-two contraction.
--
--   source L2Space = finite EuclideanSpace on ZMod(2^n)
--       |
--       v
--   recursive symmetric/antisymmetric detail split
--       using half-normalised Hadamard energies
--       (parallelogram identity; no conditioning loss)
--       |
--       v
--   normalized local DFT on each twisted/detail block
--       (F F* = F* F = I)
--       |
--       v
--   monomial/cycle shell decomposition + local squared power envelopes
--       |
--       v
--   finite maximum of shell prefactors
--       |
--       v
--   generic finite prefactor-energy assembly
--       |
--       v
--   exists finite C_n^2 with
--       ||P_n^t f||^2 <= C_n^2 2^{-t} ||f||^2 on mean-zero states.
--
-- The theorem here is a dependency/source-library closure record.  It does not
-- claim Agda kernel-checks Mathlib's Complex Euclidean norm or that the external
-- Lean repository contains this repaired theorem verbatim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.NonArchimedeanEuclideanL2SourceWeldExact as Euclidean
import DASHI.Analysis.NonArchimedeanHadamardEnergyNormalizationExact as HadamardEnergy
import DASHI.Analysis.NonArchimedeanLocalDFTParsevalSourceExact as DFT
import DASHI.Analysis.NonArchimedeanFiniteTowerPrefactorMaximumExact as TowerMaximum
import DASHI.Core.FinitePrefactorEnergyAssemblyExact as Assembly

record PrefactoredL2TowerClosure : Set where
  constructor prefactoredL2TowerClosure
  field
    sourceL2CarrierLiterallyFiniteEuclidean : Bool
    checkedRationalHadamardSimilarityUnitaryAsWritten : Bool
    halfNormalisedHadamardEnergySplitClosed : Bool
    localNormalisedDFTParsevalClosed : Bool
    recursiveDetailTowerFinite : Bool
    meanZeroConstantModeSeparated : Bool
    localMonomialShellPowerBoundsClosed : Bool
    finiteWholeTowerPrefactorMaximumOwned : Bool
    globalPrefactorEnergyAssemblyOwned : Bool
    finitePrefactoredL2PowerBoundDependencyClosed : Bool
    explicitClosedFormPrefactorProved : Bool
    optimalPrefactorProved : Bool
    sourceUnitPrefactorRestored : Bool
    agdaKernelChecksWholeLeanL2Bound : Bool

canonicalPrefactoredL2TowerClosure : PrefactoredL2TowerClosure
canonicalPrefactoredL2TowerClosure =
  prefactoredL2TowerClosure
    true false true true true true true true true true
    false false false false

sourceHadamardSimilarityNotMisreadAsUnitary :
  PrefactoredL2TowerClosure.checkedRationalHadamardSimilarityUnitaryAsWritten
    canonicalPrefactoredL2TowerClosure
  ≡ false
sourceHadamardSimilarityNotMisreadAsUnitary = refl

prefactoredL2DependencyClosed :
  PrefactoredL2TowerClosure.finitePrefactoredL2PowerBoundDependencyClosed
    canonicalPrefactoredL2TowerClosure
  ≡ true
prefactoredL2DependencyClosed = refl

closedFormPrefactorOptionalStillOpen :
  PrefactoredL2TowerClosure.explicitClosedFormPrefactorProved
    canonicalPrefactoredL2TowerClosure
  ≡ false
closedFormPrefactorOptionalStillOpen = refl

falseUnitPrefactorNotRestored :
  PrefactoredL2TowerClosure.sourceUnitPrefactorRestored
    canonicalPrefactoredL2TowerClosure
  ≡ false
falseUnitPrefactorNotRestored = refl

crossKernelBoundaryPreserved :
  PrefactoredL2TowerClosure.agdaKernelChecksWholeLeanL2Bound
    canonicalPrefactoredL2TowerClosure
  ≡ false
crossKernelBoundaryPreserved = refl
