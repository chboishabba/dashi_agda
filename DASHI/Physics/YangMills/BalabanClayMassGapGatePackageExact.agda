module DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

-- Bridge sources:
-- Tosio Kato, Perturbation Theory for Linear Operators,
-- DOI 10.1007/978-3-642-66282-9.
-- Konrad Osterwalder and Robert Schrader, Axioms for Euclidean Green's
-- Functions I/II, DOI 10.1007/BF01645738 and 10.1007/BF01608978.
-- Umberto Mosco, Convergence of Convex Sets and of Solutions of Variational
-- Inequalities, DOI 10.1016/0001-8708(69)90009-7.
-- Kazuhiro Kuwae and Takashi Shioya, Convergence of Spectral Structures,
-- DOI 10.4310/cag.2003.v11.n4.a1.
--
-- M7 was formerly one opaque "physical Hamiltonian/domain/common-core" gate.
-- The BIDI Lean/Agda pass makes the actual cut visible:
--   M7a selected finite action variation is promoted/identified with H_YM;
--   M7b H_YM has its genuine domain and common invariant dense core;
--   M7c the selected Yang--Mills form/operator is self-adjoint on that carrier.
--
-- The gauge-invariant L2 subspace is the selected carrier route.  A separate
-- quotient of configuration space by gauge orbits is therefore not itself a
-- mandatory M7 payment.  Historical quotient-route receipts remain provenance.

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

    M7aPhysicalActionVariationHamiltonianSameObject : Set
    M7bHamiltonianDomainCommonInvariantDenseCore : Set
    M7cSelfAdjointSelectedYMForm : Set

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
    m7a : M7aPhysicalActionVariationHamiltonianSameObject gates
    m7b : M7bHamiltonianDomainCommonInvariantDenseCore gates
    m7c : M7cSelfAdjointSelectedYMForm gates
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
  M7aPhysicalActionVariationHamiltonianSameObject gates →
  M7bHamiltonianDomainCommonInvariantDenseCore gates →
  M7cSelfAdjointSelectedYMForm gates →
  M8YMOSGeneratorEvolutionIdentification gates →
  M9PhysicalVacuumRecoverySystem gates →
  MandatoryClayMassGapGates gates
assembleMandatoryClayMassGapGates
    gates gate1 gate2 gate3 gate4 gate6 gate7a gate7b gate7c gate8 gate9 = record
  { m1 = gate1
  ; m2 = gate2
  ; m3 = gate3
  ; m4 = gate4
  ; m6 = gate6
  ; m7a = gate7a
  ; m7b = gate7b
  ; m7c = gate7c
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
-- Cross-prover prerequisites already paid.
------------------------------------------------------------------------

generatorUniquenessCompilerClosed :
  Frontier.generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
generatorUniquenessCompilerClosed = refl

vacuumRecoveryGapCompilerClosed :
  Frontier.vacuumOrthogonalRecoveryGapCompilerClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
vacuumRecoveryGapCompilerClosed = refl

denseCoreSpectralExclusionCompilerClosed :
  Frontier.denseCoreSpectralExclusionCompilerClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
denseCoreSpectralExclusionCompilerClosed = refl

gaugeInvariantSubspaceCarrierSelected :
  Frontier.gaugeInvariantSubspaceCarrierRouteSelected
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
gaugeInvariantSubspaceCarrierSelected = refl

gaugeOrbitConfigurationQuotientNotRequiredForSelectedCarrier :
  Frontier.gaugeOrbitConfigurationQuotientRequiredForSelectedCarrier
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
gaugeOrbitConfigurationQuotientNotRequiredForSelectedCarrier = refl

finiteSelectedHodgeVariationPairingClosed :
  Frontier.finiteSelectedHodgeVariationPairingClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ true
finiteSelectedHodgeVariationPairingClosed = refl

------------------------------------------------------------------------
-- Exact M7 frontier: the finite calculation is not the physical Hamiltonian.
------------------------------------------------------------------------

m7aPhysicalActionVariationHamiltonianSameObjectStillOpen :
  Frontier.physicalActionVariationHamiltonianSameObjectClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7aPhysicalActionVariationHamiltonianSameObjectStillOpen = refl

m7bPartialDomainHamiltonianStillOpen :
  Frontier.genuinePartialDomainHamiltonianFormalized
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7bPartialDomainHamiltonianStillOpen = refl

m7bCommonInvariantDenseCoreStillOpen :
  Frontier.commonInvariantDensePhysicalCoreConstructed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7bCommonInvariantDenseCoreStillOpen = refl

m7cSelfAdjointSelectedYMFormStillOpen :
  Frontier.physicalSelfAdjointSelectedYMFormClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
m7cSelfAdjointSelectedYMFormStillOpen = refl

massGapGateSeparationLevel : ProofLevel
massGapGateSeparationLevel = machineChecked

physicalGateProducersLevel : ProofLevel
physicalGateProducersLevel = conditional
