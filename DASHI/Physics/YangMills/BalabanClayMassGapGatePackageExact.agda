module DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact where

------------------------------------------------------------------------
-- DASHI CLAY-FACING GATES
--
-- M1 physical-scale clustering;
-- M2 dense-core spectral exclusion;
-- M3 local noncollapse;
-- M4 positivity-compatible RG, by exact OS pullback or transfer intertwining;
-- M5 optional spectral-edge detectability;
-- M6 spectral/ultraviolet compatibility;
-- M7 literal continuum YM Hamiltonian with genuine domain/common core;
-- M8 identification of the selected YM evolution/generator with the
--    OS/transfer reconstructed evolution/generator;
-- M9 physical instantiation of the already checked recovery-gap compiler.
--
-- The 2026 Lean return closes generic generator uniqueness, symmetry -> null
-- preservation, and the gauge-invariant L2 carrier.  Existing Agda closes the
-- dense-core spectral-exclusion and vacuum-orthogonal recovery-gap compilers.
-- Therefore M7--M9 are producer/identification gates, not requests to reprove
-- those generic theorems.
--
-- Sources for the added operator bridge:
-- Tosio Kato, Perturbation Theory for Linear Operators,
-- DOI 10.1007/978-3-642-66282-9.
-- Konrad Osterwalder and Robert Schrader,
-- Axioms for Euclidean Green's Functions I/II,
-- DOI 10.1007/BF01645738 and 10.1007/BF01608978.
-- Umberto Mosco, Convergence of Convex Sets and of Solutions of Variational
-- Inequalities, DOI 10.1016/0001-8708(69)90009-7.
-- Kazuhiro Kuwae and Takashi Shioya, Convergence of Spectral Structures,
-- DOI 10.4310/cag.2003.v11.n4.a1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayPhysicalScaleExponentExact
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact
import DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact
import DASHI.Physics.YangMills.BalabanClayObservableGapEdgeExact
import DASHI.Physics.YangMills.BalabanClaySpectralUVCompatibilityExact
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

infixr 4 _or_
data _or_ (A B : Set) : Set where
  leftRoute : A → A or B
  rightRoute : B → A or B

record ClayMassGapGatePropositions : Set₁ where
  field
    M1PhysicalScaleClustering : Set
    M2DenseCoreSpectralExclusion : Set
    M3LocalNoncollapse : Set
    M4ExactOSPullback : Set
    M4TransferIntertwining : Set
    M5ObservableDetectsGapEdge : Set
    M6SpectralUVCompatibility : Set

    -- New terminal weld: transfer/OS gap data is not silently identified with
    -- the physical unbounded Yang--Mills Hamiltonian.
    M7PhysicalHamiltonianDomainCommonCore : Set
    M8YMOSGeneratorEvolutionIdentification : Set
    M9PhysicalVacuumRecoverySystem : Set

open ClayMassGapGatePropositions public

record MandatoryClayMassGapGates
    (gates : ClayMassGapGatePropositions) : Set₁ where
  field
    m1 : M1PhysicalScaleClustering gates
    m2 : M2DenseCoreSpectralExclusion gates
    m3 : M3LocalNoncollapse gates
    m4 : M4ExactOSPullback gates or M4TransferIntertwining gates
    m6 : M6SpectralUVCompatibility gates
    m7 : M7PhysicalHamiltonianDomainCommonCore gates
    m8 : M8YMOSGeneratorEvolutionIdentification gates
    m9 : M9PhysicalVacuumRecoverySystem gates

open MandatoryClayMassGapGates public

record SharpMassIdentification
    (gates : ClayMassGapGatePropositions) : Set₁ where
  field
    mandatory : MandatoryClayMassGapGates gates
    m5 : M5ObservableDetectsGapEdge gates

open SharpMassIdentification public

assembleMandatoryClayMassGapGates :
  ∀ gates →
  M1PhysicalScaleClustering gates →
  M2DenseCoreSpectralExclusion gates →
  M3LocalNoncollapse gates →
  (M4ExactOSPullback gates or M4TransferIntertwining gates) →
  M6SpectralUVCompatibility gates →
  M7PhysicalHamiltonianDomainCommonCore gates →
  M8YMOSGeneratorEvolutionIdentification gates →
  M9PhysicalVacuumRecoverySystem gates →
  MandatoryClayMassGapGates gates
assembleMandatoryClayMassGapGates
  gates gate1 gate2 gate3 gate4 gate6 gate7 gate8 gate9 = record
  { m1 = gate1
  ; m2 = gate2
  ; m3 = gate3
  ; m4 = gate4
  ; m6 = gate6
  ; m7 = gate7
  ; m8 = gate8
  ; m9 = gate9
  }

addOptionalSpectralEdgeIdentification :
  ∀ {gates} →
  MandatoryClayMassGapGates gates →
  M5ObservableDetectsGapEdge gates →
  SharpMassIdentification gates
addOptionalSpectralEdgeIdentification mandatoryGates gate5 = record
  { mandatory = mandatoryGates
  ; m5 = gate5
  }

------------------------------------------------------------------------
-- Closed generic machinery consumed by M7--M9.
------------------------------------------------------------------------

generatorUniquenessCompilerClosed :
  Frontier.generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ true
generatorUniquenessCompilerClosed = refl

vacuumRecoveryGapCompilerClosed :
  Frontier.vacuumOrthogonalRecoveryGapCompilerClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ true
vacuumRecoveryGapCompilerClosed = refl

denseCoreSpectralExclusionCompilerClosed :
  Frontier.denseCoreSpectralExclusionCompilerClosed
    Frontier.canonicalYMOperatorContinuumFrontier
  ≡ true
denseCoreSpectralExclusionCompilerClosed = refl

massGapGateSeparationLevel : ProofLevel
massGapGateSeparationLevel = machineChecked

physicalGateProducersLevel : ProofLevel
physicalGateProducersLevel = conditional
