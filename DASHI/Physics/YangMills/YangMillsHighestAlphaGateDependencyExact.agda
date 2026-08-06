module DASHI.Physics.YangMills.YangMillsHighestAlphaGateDependencyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned; published in The Millennium Prize Problems.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II".
-- DOI: 10.1007/BF01608978.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
-- Encode the strict mathematical dependency order identified by the completed
-- finite algebra and countermodels.  A finite propagator is not an all-scale
-- gap; an all-scale lattice gap is not a continuum OS theory; a continuum OS
-- theory is not yet a Hamiltonian mass-gap theorem; an SU(2) theorem is not the
-- required all-compact-simple-group theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

data HighestAlphaGate : Set where
  kernelCheckedUnifiedHead : HighestAlphaGate
  selectedBackgroundTerminalHessian : HighestAlphaGate
  finiteBackgroundPropagator : HighestAlphaGate
  physicalUniformRGStep : HighestAlphaGate
  interactingEuclideanMeasure : HighestAlphaGate
  thermodynamicContinuumOSLimit : HighestAlphaGate
  reconstructedHamiltonianMassGap : HighestAlphaGate
  allCompactSimpleGroups : HighestAlphaGate

nextGate : HighestAlphaGate → HighestAlphaGate
nextGate kernelCheckedUnifiedHead = selectedBackgroundTerminalHessian
nextGate selectedBackgroundTerminalHessian = finiteBackgroundPropagator
nextGate finiteBackgroundPropagator = physicalUniformRGStep
nextGate physicalUniformRGStep = interactingEuclideanMeasure
nextGate interactingEuclideanMeasure = thermodynamicContinuumOSLimit
nextGate thermodynamicContinuumOSLimit = reconstructedHamiltonianMassGap
nextGate reconstructedHamiltonianMassGap = allCompactSimpleGroups
nextGate allCompactSimpleGroups = allCompactSimpleGroups

remainingGateCount : HighestAlphaGate → Nat
remainingGateCount kernelCheckedUnifiedHead = 7
remainingGateCount selectedBackgroundTerminalHessian = 6
remainingGateCount finiteBackgroundPropagator = 5
remainingGateCount physicalUniformRGStep = 4
remainingGateCount interactingEuclideanMeasure = 3
remainingGateCount thermodynamicContinuumOSLimit = 2
remainingGateCount reconstructedHamiltonianMassGap = 1
remainingGateCount allCompactSimpleGroups = 0

initialGateCountExact :
  remainingGateCount kernelCheckedUnifiedHead ≡ 7
initialGateCountExact = refl

finitePropagatorIsNotClayCompletion :
  finiteBackgroundPropagator ≡ allCompactSimpleGroups → ⊥
finitePropagatorIsNotClayCompletion ()

uniformRGIsNotContinuumOS :
  physicalUniformRGStep ≡ thermodynamicContinuumOSLimit → ⊥
uniformRGIsNotContinuumOS ()

continuumOSIsNotMassGap :
  thermodynamicContinuumOSLimit ≡ reconstructedHamiltonianMassGap → ⊥
continuumOSIsNotMassGap ()

su2EndpointIsNotAllGroups :
  reconstructedHamiltonianMassGap ≡ allCompactSimpleGroups → ⊥
su2EndpointIsNotAllGroups ()

data LoadBearingObligation : Set where
  selectedBackgroundRadius : LoadBearingObligation
  selectedBackgroundCorrelatedWLocal : LoadBearingObligation
  literalHessianMatrixStencil : LoadBearingObligation
  constructiveFiniteInverse : LoadBearingObligation
  physicalSchurHessianIdentity : LoadBearingObligation
  uniformFluctuationInverseDecay : LoadBearingObligation
  uniformCoarseFineBlockControl : LoadBearingObligation
  signedRemainderAndStrictLoss : LoadBearingObligation
  largeFieldPolymerClusterConvergence : LoadBearingObligation
  thermodynamicAndUltravioletLimits : LoadBearingObligation
  continuumOSAxiomsAndNontriviality : LoadBearingObligation
  observableDensityAndSpectralTransfer : LoadBearingObligation
  compactSimpleGroupParameterization : LoadBearingObligation

obligationGate : LoadBearingObligation → HighestAlphaGate
obligationGate selectedBackgroundRadius = selectedBackgroundTerminalHessian
obligationGate selectedBackgroundCorrelatedWLocal = selectedBackgroundTerminalHessian
obligationGate literalHessianMatrixStencil = finiteBackgroundPropagator
obligationGate constructiveFiniteInverse = finiteBackgroundPropagator
obligationGate physicalSchurHessianIdentity = physicalUniformRGStep
obligationGate uniformFluctuationInverseDecay = physicalUniformRGStep
obligationGate uniformCoarseFineBlockControl = physicalUniformRGStep
obligationGate signedRemainderAndStrictLoss = physicalUniformRGStep
obligationGate largeFieldPolymerClusterConvergence = interactingEuclideanMeasure
obligationGate thermodynamicAndUltravioletLimits = thermodynamicContinuumOSLimit
obligationGate continuumOSAxiomsAndNontriviality = thermodynamicContinuumOSLimit
obligationGate observableDensityAndSpectralTransfer = reconstructedHamiltonianMassGap
obligationGate compactSimpleGroupParameterization = allCompactSimpleGroups

record ClayCompletionTarget : Set₁ where
  field
    GateWitness : HighestAlphaGate → Set
    unifiedHead : GateWitness kernelCheckedUnifiedHead
    terminalHessian : GateWitness selectedBackgroundTerminalHessian
    finitePropagator : GateWitness finiteBackgroundPropagator
    uniformRG : GateWitness physicalUniformRGStep
    euclideanMeasure : GateWitness interactingEuclideanMeasure
    continuumOS : GateWitness thermodynamicContinuumOSLimit
    massGap : GateWitness reconstructedHamiltonianMassGap
    allGroups : GateWitness allCompactSimpleGroups

-- No canonical inhabitant is supplied.  The preceding modules advance exact
-- sublemmas while the physical and continuum witnesses remain open.
