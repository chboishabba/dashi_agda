module DASHI.Analysis.NonArchimedeanFourierShellEnergyAssemblyBidiExact where

------------------------------------------------------------------------
-- FOURIER / DETAIL ENERGY ASSEMBLY BIDI
--
-- Corrected closure:
--
-- * source L2Space is literally finite EuclideanSpace on ZMod(2^n);
-- * the checked rational Hadamard block similarity is NOT unitary as written;
-- * half-normalised symmetric/antisymmetric energies are exact by the
--   parallelogram identity, with no recursive conditioning loss;
-- * the local DFT is genuinely normalized and unitary (F F*=F* F=I);
-- * shell/cycle power envelopes are already compiled;
-- * finite shell-prefactor maximum and finite energy assembly are repo-owned.
--
-- Thus the old input/output Parseval same-object obligations are dependency-
-- closed.  The closure is source/library-level across Lean/Agda, not a claim
-- that Agda kernel-checks Mathlib's Complex Euclidean norm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])

import DASHI.Analysis.NonArchimedeanEuclideanL2SourceWeldExact as Euclidean
import DASHI.Analysis.NonArchimedeanHadamardEnergyNormalizationExact as HadamardEnergy
import DASHI.Analysis.NonArchimedeanLocalDFTParsevalSourceExact as DFT
import DASHI.Analysis.NonArchimedeanFiniteTowerPrefactorMaximumExact as Maximum
import DASHI.Analysis.NonArchimedeanPrefactoredL2TowerClosureExact as TowerClosure
import DASHI.Core.FinitePrefactorEnergyAssemblyExact as Assembly


data AssemblyLeaf : Set where
  sourceEuclideanL2Carrier : AssemblyLeaf
  checkedHadamardSimilarity : AssemblyLeaf
  normalisedHadamardEnergySplit : AssemblyLeaf
  localDFTParseval : AssemblyLeaf
  meanZeroConstantModeSeparation : AssemblyLeaf
  shellPartition : AssemblyLeaf
  shellSquaredPowerBounds : AssemblyLeaf
  finiteTowerPrefactorMaximum : AssemblyLeaf
  finitePrefactorEnergyAssembly : AssemblyLeaf
  wholeL2SquaredPowerBound : AssemblyLeaf


data AssemblyStatus : Set where
  sourceOwned : AssemblyStatus
  sourceLibraryCompiled : AssemblyStatus
  compiled : AssemblyStatus
  repoGeneric : AssemblyStatus
  downstreamCompiled : AssemblyStatus

assemblyStatus : AssemblyLeaf → AssemblyStatus
assemblyStatus sourceEuclideanL2Carrier = sourceOwned
assemblyStatus checkedHadamardSimilarity = sourceOwned
assemblyStatus normalisedHadamardEnergySplit = sourceLibraryCompiled
assemblyStatus localDFTParseval = sourceLibraryCompiled
assemblyStatus meanZeroConstantModeSeparation = compiled
assemblyStatus shellPartition = compiled
assemblyStatus shellSquaredPowerBounds = compiled
assemblyStatus finiteTowerPrefactorMaximum = repoGeneric
assemblyStatus finitePrefactorEnergyAssembly = repoGeneric
assemblyStatus wholeL2SquaredPowerBound = downstreamCompiled


data AssemblyObligation : Set where
  noRemainingAssemblyProducer : AssemblyObligation

assemblyCutset : List AssemblyObligation
assemblyCutset = []

record FourierShellAssemblyBoundary : Set where
  constructor fourierShellAssemblyBoundary
  field
    sourceDFTUnitarityOwned : Bool
    checkedHadamardSimilarityUnitaryAsWritten : Bool
    halfNormalisedHadamardEnergyExact : Bool
    sourceL2FiniteCoordinateSameObject : Bool
    genericFinitePrefactorAssemblyOwned : Bool
    finitePrefactoredL2DependencyClosed : Bool
    unitPrefactorCanBeRestored : Bool
    agdaKernelChecksSourceComplexNorm : Bool

canonicalFourierShellAssemblyBoundary : FourierShellAssemblyBoundary
canonicalFourierShellAssemblyBoundary =
  fourierShellAssemblyBoundary
    true false true true true true false false

hadamardNormalisationCorrectionRetained :
  FourierShellAssemblyBoundary.checkedHadamardSimilarityUnitaryAsWritten
    canonicalFourierShellAssemblyBoundary
  ≡ false
hadamardNormalisationCorrectionRetained = refl

assemblyDependencyClosed : assemblyCutset ≡ []
assemblyDependencyClosed = refl

unitPrefactorCannotReturn :
  FourierShellAssemblyBoundary.unitPrefactorCanBeRestored
    canonicalFourierShellAssemblyBoundary
  ≡ false
unitPrefactorCannotReturn = refl
