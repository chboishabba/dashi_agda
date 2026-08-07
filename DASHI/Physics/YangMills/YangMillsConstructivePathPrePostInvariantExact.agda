module DASHI.Physics.YangMills.YangMillsConstructivePathPrePostInvariantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- Tadeusz Balaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field".
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Balaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I".
-- DOI: 10.1007/BF01215223.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling".
-- DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- Convert the existing highest-alpha dependency chain into explicit contracts.
-- Every gate now has named preconditions, postconditions and invariants.  A
-- separate repository-status map distinguishes exact algebra already present,
-- conditional interfaces, genuinely open physical producers and standard
-- external reconstruction theorems.
--
-- The two current routes remain distinct:
--
--   A. selected background -> finite propagator -> scale-uniform RG;
--   B. strong-coupling Bakry--Emery -> fixed-spacing thermodynamic clustering.
--
-- Route B does not by itself provide changing-spacing ultraviolet control,
-- continuum local-operator/OPE matching, continuum OS limits or a Hamiltonian
-- spectral gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.YangMillsHighestAlphaGateDependencyExact as Gate
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

------------------------------------------------------------------------
-- Repository-owned mathematical clauses.
------------------------------------------------------------------------

data PathClause : Set where
  cumulativeSourceHead : PathClause
  observedAgdaKernelAcceptance : PathClause
  selectedBackgroundLinkRadius : PathClause
  selectedBackgroundCorrelatedWilsonLower : PathClause
  terminalOneThirtySecondHessianCoercivity : PathClause
  literalHessianMatrixAndHermiticity : PathClause
  literalHessianStencilAndRowColumnMass : PathClause
  constructiveFiniteHessianInverse : PathClause
  finiteCombesThomasGreenDecay : PathClause
  differentiatedPhysicalSchurIdentity : PathClause
  uniformFluctuationCoercivityAndInverseDecay : PathClause
  uniformCoarseFineBlockBounds : PathClause
  signedRemainderStrictLossContraction : PathClause
  physicalRGGoodClassPreservation : PathClause
  interactingFiniteVolumeMeasure : PathClause
  largeFieldPolymerClusterConvergence : PathClause
  thermodynamicLimit : PathClause
  ultravioletChangingSpacingLimit : PathClause
  continuumGaugeInvariantCurvatureOperators : PathClause
  continuumShortDistanceAsymptoticFreedomOPE : PathClause
  continuumOSAxioms : PathClause
  continuumNontriviality : PathClause
  vacuumCompatibleSpectralTransfer : PathClause
  positiveHamiltonianMassGap : PathClause
  allCompactSimpleGroupConstruction : PathClause

data ClauseState : Set where
  exactInRepository : ClauseState
  conditionalEndpointInRepository : ClauseState
  openPhysicalProducer : ClauseState
  externalStandardTheoremNeedsInstantiation : ClauseState

clauseState : PathClause → ClauseState
clauseState cumulativeSourceHead = exactInRepository
clauseState observedAgdaKernelAcceptance = openPhysicalProducer
clauseState selectedBackgroundLinkRadius = openPhysicalProducer
clauseState selectedBackgroundCorrelatedWilsonLower = openPhysicalProducer
clauseState terminalOneThirtySecondHessianCoercivity = conditionalEndpointInRepository
clauseState literalHessianMatrixAndHermiticity = openPhysicalProducer
clauseState literalHessianStencilAndRowColumnMass = openPhysicalProducer
clauseState constructiveFiniteHessianInverse = openPhysicalProducer
clauseState finiteCombesThomasGreenDecay = conditionalEndpointInRepository
clauseState differentiatedPhysicalSchurIdentity = openPhysicalProducer
clauseState uniformFluctuationCoercivityAndInverseDecay = openPhysicalProducer
clauseState uniformCoarseFineBlockBounds = openPhysicalProducer
clauseState signedRemainderStrictLossContraction = openPhysicalProducer
clauseState physicalRGGoodClassPreservation = conditionalEndpointInRepository
clauseState interactingFiniteVolumeMeasure = openPhysicalProducer
clauseState largeFieldPolymerClusterConvergence = openPhysicalProducer
clauseState thermodynamicLimit = openPhysicalProducer
clauseState ultravioletChangingSpacingLimit = openPhysicalProducer
clauseState continuumGaugeInvariantCurvatureOperators = openPhysicalProducer
clauseState continuumShortDistanceAsymptoticFreedomOPE = openPhysicalProducer
clauseState continuumOSAxioms = externalStandardTheoremNeedsInstantiation
clauseState continuumNontriviality = openPhysicalProducer
clauseState vacuumCompatibleSpectralTransfer = openPhysicalProducer
clauseState positiveHamiltonianMassGap = openPhysicalProducer
clauseState allCompactSimpleGroupConstruction = openPhysicalProducer

------------------------------------------------------------------------
-- Gate contracts.
------------------------------------------------------------------------

record StageContract : Set where
  constructor stageContract
  field
    preconditions : List PathClause
    postconditions : List PathClause
    invariants : List Clay.ClayInvariant

open StageContract public

kernelPost : List PathClause
kernelPost = cumulativeSourceHead ∷ observedAgdaKernelAcceptance ∷ []

terminalHessianPost : List PathClause
terminalHessianPost =
  selectedBackgroundLinkRadius
  ∷ selectedBackgroundCorrelatedWilsonLower
  ∷ terminalOneThirtySecondHessianCoercivity
  ∷ []

finitePropagatorPost : List PathClause
finitePropagatorPost =
  literalHessianMatrixAndHermiticity
  ∷ literalHessianStencilAndRowColumnMass
  ∷ constructiveFiniteHessianInverse
  ∷ finiteCombesThomasGreenDecay
  ∷ []

uniformRGPost : List PathClause
uniformRGPost =
  differentiatedPhysicalSchurIdentity
  ∷ uniformFluctuationCoercivityAndInverseDecay
  ∷ uniformCoarseFineBlockBounds
  ∷ signedRemainderStrictLossContraction
  ∷ physicalRGGoodClassPreservation
  ∷ []

euclideanMeasurePost : List PathClause
euclideanMeasurePost =
  interactingFiniteVolumeMeasure
  ∷ largeFieldPolymerClusterConvergence
  ∷ []

continuumOSPost : List PathClause
continuumOSPost =
  thermodynamicLimit
  ∷ ultravioletChangingSpacingLimit
  ∷ continuumGaugeInvariantCurvatureOperators
  ∷ continuumShortDistanceAsymptoticFreedomOPE
  ∷ continuumOSAxioms
  ∷ continuumNontriviality
  ∷ []

hamiltonianGapPost : List PathClause
hamiltonianGapPost =
  vacuumCompatibleSpectralTransfer
  ∷ positiveHamiltonianMassGap
  ∷ []

allGroupsPost : List PathClause
allGroupsPost = allCompactSimpleGroupConstruction ∷ []

finiteInvariants : List Clay.ClayInvariant
finiteInvariants =
  Clay.gaugeSymmetryPreserved
  ∷ Clay.localityPreserved
  ∷ Clay.targetGapAndClusteringNotAssumedAsInputs
  ∷ []

measureInvariants : List Clay.ClayInvariant
measureInvariants =
  Clay.gaugeSymmetryPreserved
  ∷ Clay.localityPreserved
  ∷ Clay.measurePositivityAndNormalizationPreserved
  ∷ Clay.targetGapAndClusteringNotAssumedAsInputs
  ∷ []

continuumInvariants : List Clay.ClayInvariant
continuumInvariants =
  Clay.gaugeSymmetryPreserved
  ∷ Clay.localityPreserved
  ∷ Clay.euclideanCovariancePreserved
  ∷ Clay.reflectionPositivityPreserved
  ∷ Clay.measurePositivityAndNormalizationPreserved
  ∷ Clay.volumeAndCutoffCompatibilityPreserved
  ∷ Clay.physicalScaleLowerBoundUniform
  ∷ Clay.nontrivialityPreservedInTheLimit
  ∷ Clay.targetGapAndClusteringNotAssumedAsInputs
  ∷ []

spectralInvariants : List Clay.ClayInvariant
spectralInvariants =
  Clay.reflectionPositivityPreserved
  ∷ Clay.physicalScaleLowerBoundUniform
  ∷ Clay.noSpectralPollutionBelowGap
  ∷ Clay.nontrivialityPreservedInTheLimit
  ∷ []

contractFor : Gate.HighestAlphaGate → StageContract
contractFor Gate.kernelCheckedUnifiedHead =
  stageContract [] kernelPost finiteInvariants
contractFor Gate.selectedBackgroundTerminalHessian =
  stageContract kernelPost terminalHessianPost finiteInvariants
contractFor Gate.finiteBackgroundPropagator =
  stageContract terminalHessianPost finitePropagatorPost finiteInvariants
contractFor Gate.physicalUniformRGStep =
  stageContract finitePropagatorPost uniformRGPost finiteInvariants
contractFor Gate.interactingEuclideanMeasure =
  stageContract uniformRGPost euclideanMeasurePost measureInvariants
contractFor Gate.thermodynamicContinuumOSLimit =
  stageContract euclideanMeasurePost continuumOSPost continuumInvariants
contractFor Gate.reconstructedHamiltonianMassGap =
  stageContract continuumOSPost hamiltonianGapPost spectralInvariants
contractFor Gate.allCompactSimpleGroups =
  stageContract hamiltonianGapPost allGroupsPost
    (Clay.compactSimpleGroupParameterizationPreserved
      ∷ spectralInvariants)

kernelToTerminalInterfaceExact :
  preconditions (contractFor Gate.selectedBackgroundTerminalHessian)
  ≡ postconditions (contractFor Gate.kernelCheckedUnifiedHead)
kernelToTerminalInterfaceExact = refl

terminalToPropagatorInterfaceExact :
  preconditions (contractFor Gate.finiteBackgroundPropagator)
  ≡ postconditions (contractFor Gate.selectedBackgroundTerminalHessian)
terminalToPropagatorInterfaceExact = refl

propagatorToRGInterfaceExact :
  preconditions (contractFor Gate.physicalUniformRGStep)
  ≡ postconditions (contractFor Gate.finiteBackgroundPropagator)
propagatorToRGInterfaceExact = refl

rgToMeasureInterfaceExact :
  preconditions (contractFor Gate.interactingEuclideanMeasure)
  ≡ postconditions (contractFor Gate.physicalUniformRGStep)
rgToMeasureInterfaceExact = refl

measureToContinuumInterfaceExact :
  preconditions (contractFor Gate.thermodynamicContinuumOSLimit)
  ≡ postconditions (contractFor Gate.interactingEuclideanMeasure)
measureToContinuumInterfaceExact = refl

continuumToGapInterfaceExact :
  preconditions (contractFor Gate.reconstructedHamiltonianMassGap)
  ≡ postconditions (contractFor Gate.thermodynamicContinuumOSLimit)
continuumToGapInterfaceExact = refl

gapToAllGroupsInterfaceExact :
  preconditions (contractFor Gate.allCompactSimpleGroups)
  ≡ postconditions (contractFor Gate.reconstructedHamiltonianMassGap)
gapToAllGroupsInterfaceExact = refl

------------------------------------------------------------------------
-- Route separation.
------------------------------------------------------------------------

data ConstructiveRouteCapability : Set where
  selectedBackgroundFinitePropagatorCapability : ConstructiveRouteCapability
  selectedBackgroundScaleUniformRGCapability : ConstructiveRouteCapability
  strongCouplingFixedSpacingLSICapability : ConstructiveRouteCapability
  strongCouplingFixedSpacingClusteringCapability : ConstructiveRouteCapability
  changingSpacingUltravioletCapability : ConstructiveRouteCapability
  continuumOperatorOPECapability : ConstructiveRouteCapability
  continuumOSCapability : ConstructiveRouteCapability
  HamiltonianMassGapCapability : ConstructiveRouteCapability

strongCouplingClusteringIsNotUltravioletControl :
  strongCouplingFixedSpacingClusteringCapability
  ≡ changingSpacingUltravioletCapability → ⊥
strongCouplingClusteringIsNotUltravioletControl ()

strongCouplingClusteringIsNotOperatorOPE :
  strongCouplingFixedSpacingClusteringCapability
  ≡ continuumOperatorOPECapability → ⊥
strongCouplingClusteringIsNotOperatorOPE ()

strongCouplingClusteringIsNotContinuumOS :
  strongCouplingFixedSpacingClusteringCapability
  ≡ continuumOSCapability → ⊥
strongCouplingClusteringIsNotContinuumOS ()

strongCouplingClusteringIsNotHamiltonianGap :
  strongCouplingFixedSpacingClusteringCapability
  ≡ HamiltonianMassGapCapability → ⊥
strongCouplingClusteringIsNotHamiltonianGap ()

finitePropagatorIsNotUniformRG :
  selectedBackgroundFinitePropagatorCapability
  ≡ selectedBackgroundScaleUniformRGCapability → ⊥
finitePropagatorIsNotUniformRG ()
