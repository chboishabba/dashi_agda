module DASHI.Analysis.NonArchimedeanFourierShellEnergyAssemblyBidiExact where

------------------------------------------------------------------------
-- FOURIER SHELL ENERGY ASSEMBLY BIDI
--
-- Source/repo ingredients already available:
--
--   * `fourierBasisMatrix_mul_star`: theorem-bearing DFT unitarity;
--   * checked dyadic/detail resolution of identity;
--   * monomial character action and shell/cycle partition;
--   * explicit shell squared prefactor compiler;
--   * generic finite component inequality assembly in
--       DASHI.Core.FiniteComponentEnergyAssemblyExact.
--
-- The remaining same-object seam is not abstract orthogonality.  It is the
-- concrete identification of the source L2 squared norm with the finite list of
-- Fourier-shell energies consumed by the generic assembly theorem, before and
-- after P_n^t.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.FiniteComponentEnergyAssemblyExact as Assembly
import DASHI.Analysis.NonArchimedeanExplicitSquaredMixingPrefactorExact as Prefactor


data AssemblyLeaf : Set where
  dftUnitary : AssemblyLeaf
  detailResolutionIdentity : AssemblyLeaf
  meanZeroExcludesPerronCharacter : AssemblyLeaf
  shellPartition : AssemblyLeaf
  shellSquaredPowerBounds : AssemblyLeaf
  finiteComponentSumCompiler : AssemblyLeaf
  inputNormEqualsShellEnergySum : AssemblyLeaf
  outputNormEqualsShellEnergySum : AssemblyLeaf
  wholeL2SquaredPowerBound : AssemblyLeaf


data AssemblyStatus : Set where
  sourceOwned : AssemblyStatus
  compiled : AssemblyStatus
  repoGeneric : AssemblyStatus
  liveSameObject : AssemblyStatus
  downstream : AssemblyStatus

assemblyStatus : AssemblyLeaf → AssemblyStatus
assemblyStatus dftUnitary = sourceOwned
assemblyStatus detailResolutionIdentity = sourceOwned
assemblyStatus meanZeroExcludesPerronCharacter = compiled
assemblyStatus shellPartition = compiled
assemblyStatus shellSquaredPowerBounds = compiled
assemblyStatus finiteComponentSumCompiler = repoGeneric
assemblyStatus inputNormEqualsShellEnergySum = liveSameObject
assemblyStatus outputNormEqualsShellEnergySum = liveSameObject
assemblyStatus wholeL2SquaredPowerBound = downstream


data AssemblyObligation : Set where
  needInputParsevalShellEnergyWeld : AssemblyObligation
  needOutputParsevalShellEnergyWeld : AssemblyObligation

assemblyCutset : List AssemblyObligation
assemblyCutset =
  needInputParsevalShellEnergyWeld ∷
  needOutputParsevalShellEnergyWeld ∷
  []

record FourierShellAssemblyBoundary : Set where
  constructor fourierShellAssemblyBoundary
  field
    sourceDFTUnitarityAlreadyOwned : Bool
    genericFiniteSumInequalityNeedsReproof : Bool
    shellEnergySameObjectWeldsStillNeeded : Bool
    eigenvalueRadiusCanReplacePowerNormWeld : Bool
    unitPrefactorCanBeRestored : Bool

canonicalFourierShellAssemblyBoundary : FourierShellAssemblyBoundary
canonicalFourierShellAssemblyBoundary =
  fourierShellAssemblyBoundary true false true false false

assemblyInfrastructureAlreadyOwned :
  FourierShellAssemblyBoundary.genericFiniteSumInequalityNeedsReproof
    canonicalFourierShellAssemblyBoundary
  ≡ false
assemblyInfrastructureAlreadyOwned = refl

sameObjectEnergyWeldStillLive :
  FourierShellAssemblyBoundary.shellEnergySameObjectWeldsStillNeeded
    canonicalFourierShellAssemblyBoundary
  ≡ true
sameObjectEnergyWeldStillLive = refl

unitPrefactorCannotReturn :
  FourierShellAssemblyBoundary.unitPrefactorCanBeRestored
    canonicalFourierShellAssemblyBoundary
  ≡ false
unitPrefactorCannotReturn = refl
