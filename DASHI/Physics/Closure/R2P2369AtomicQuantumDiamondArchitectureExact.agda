module DASHI.Physics.Closure.R2P2369AtomicQuantumDiamondArchitectureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact as R2P2
import DASHI.Physics.Closure.R2P2369WaveOpticalCombInformationCutExact as WaveCut
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as SymbolicR2P2
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as CoreR2P2
import Data.Empty as EmptyR2P2
import DASHI.Physics.Closure.R2P2ClockBiasIdentifiabilityMaxCutExact as Bias
import DASHI.Physics.Closure.R2P2ThreeClockLoopClosure369Exact as Loop
import DASHI.Physics.Closure.R2P2OpticalLattice369HamiltonianCutExact as Lattice
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift
import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as SI
import DASHI.Physics.Closure.QuantumClockSuperpositionReceipt as Superposition
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic
import DASHI.Core.SuperSSP369Field as Field369
import DASHI.Foundations.Base369BinaryTernaryRefinement as Refine
import DASHI.Foundations.Base369PolyphaseCharacters as C3
import DASHI.Physics.Closure.Base369PolyphaseKernelBoundary as Kernel
import DASHI.Geometry.FiniteCausalDiamond as Diamond
import DASHI.Algebra.Quantum.QutritWeyl as Qutrit
import DASHI.Physics.Optics.OpticalPhenomenaKernelBridge as Optics

------------------------------------------------------------------------
-- O: Model the full *logical* pipeline from atomic species to gravity
--    comparison, using existing 369 and diamond constructors.
-- R: Reuse owners; never identify a 3-state classical index with Yb atom
--    physics, 369 field with an actual EM field, or finite causal poset with
--    a measured Lorentz metric. Neither constructor produces a device.
-- C: Construct indexed stages, model fields, exact finite refinement,
--    source identities, and documented conditional data dependencies.
-- S: Keep physical hardware, calibration, link reciprocity, geopotential,
--    measured frequency ratios and QG discrimination external.
-- P: Theorems below are definitional finite model statements only.
-- G: Einstein, Hall/Haensch/Diddams, R2P2 collaboration and earlier DASHI
--    module and PR owners retain priority.
-- F: This file must be Agda-kernel-checked before calling it verified.
------------------------------------------------------------------------

data PipelineStage : Set where
  sourceAndStandards : PipelineStage
  atomicIdentity : PipelineStage
  coolingAndTrap : PipelineStage
  opticalInterrogation : PipelineStage
  frequencyCombReadout : PipelineStage
  hybridPhaseTransfer : PipelineStage
  geopotentialComparison : PipelineStage
  uncertaintyAnalysis : PipelineStage
  gravityDecision : PipelineStage

data StageStep : PipelineStage → PipelineStage → Set where
  standardsToAtomic : StageStep sourceAndStandards atomicIdentity
  atomicToPreparation : StageStep atomicIdentity coolingAndTrap
  preparationToInterrogation : StageStep coolingAndTrap opticalInterrogation
  interrogationToComb : StageStep opticalInterrogation frequencyCombReadout
  combToTransfer : StageStep frequencyCombReadout hybridPhaseTransfer
  transferToGeopotential : StageStep hybridPhaseTransfer geopotentialComparison
  geopotentialToUncertainty : StageStep geopotentialComparison uncertaintyAnalysis
  uncertaintyToDecision : StageStep uncertaintyAnalysis gravityDecision

record ClockPipelinePath : Set where
  field
    stage1 : StageStep sourceAndStandards atomicIdentity
    stage2 : StageStep atomicIdentity coolingAndTrap
    stage3 : StageStep coolingAndTrap opticalInterrogation
    stage4 : StageStep opticalInterrogation frequencyCombReadout
    stage5 : StageStep frequencyCombReadout hybridPhaseTransfer
    stage6 : StageStep hybridPhaseTransfer geopotentialComparison
    stage7 : StageStep geopotentialComparison uncertaintyAnalysis
    stage8 : StageStep uncertaintyAnalysis gravityDecision

canonicalClockPipelinePath : ClockPipelinePath
canonicalClockPipelinePath = record
  { stage1 = standardsToAtomic
  ; stage2 = atomicToPreparation
  ; stage3 = preparationToInterrogation
  ; stage4 = interrogationToComb
  ; stage5 = combToTransfer
  ; stage6 = transferToGeopotential
  ; stage7 = geopotentialToUncertainty
  ; stage8 = uncertaintyToDecision
  }

------------------------------------------------------------------------
-- Selected *isotope model* identities, not two verified instrument records.
-- Video gives 171Yb for the atomic lattice-clock explanation, while the
-- APS R2P2 abstract only states neutral ytterbium without isotope IDs.
-- 171Yb: atomic Z=70, N=101. Cs133: Z=55, N=78.
-- Neither isotope selection nor neutrality derives an optical transition.
------------------------------------------------------------------------

record AtomicClockIdentities : Set where
  field
    mountainYb171 : Atomic.AtomicIndex
    mountainIsYb171 : mountainYb171 ≡ Atomic.neutralAt 70 101
    mountainNeutral : Atomic.Neutral mountainYb171

    boulderYb171 : Atomic.AtomicIndex
    boulderIsYb171 : boulderYb171 ≡ Atomic.neutralAt 70 101
    boulderNeutral : Atomic.Neutral boulderYb171

    siCs133 : Atomic.AtomicIndex
    cesiumIs133 : siCs133 ≡ Atomic.neutralAt 55 78
    cesiumNeutral : Atomic.Neutral siCs133

    cesiumSecond : SI.Cs133SISecondAnchor
    cesiumSecondCanonical :
      cesiumSecond ≡ SI.canonicalCs133SISecondAnchor

    bothR2P2IsotopesIndependentlyVerifiedFromAPS : Bool
    bothIsotopesNotVerifiedByAPS :
      bothR2P2IsotopesIndependentlyVerifiedFromAPS ≡ false

    isotopeIdentityDerivesOpticalTransition : Bool
    isotopeIdentityDoesNotDeriveOpticalTransition :
      isotopeIdentityDerivesOpticalTransition ≡ false

open AtomicClockIdentities public

canonicalAtomicClockIdentities : AtomicClockIdentities
canonicalAtomicClockIdentities = record
  { mountainYb171 = Atomic.neutralAt 70 101
  ; mountainIsYb171 = refl
  ; mountainNeutral = Atomic.neutralAtIsNeutral 70 101
  ; boulderYb171 = Atomic.neutralAt 70 101
  ; boulderIsYb171 = refl
  ; boulderNeutral = Atomic.neutralAtIsNeutral 70 101
  ; siCs133 = Atomic.neutralAt 55 78
  ; cesiumIs133 = refl
  ; cesiumNeutral = Atomic.neutralAtIsNeutral 55 78
  ; cesiumSecond = SI.canonicalCs133SISecondAnchor
  ; cesiumSecondCanonical = refl
  ; bothR2P2IsotopesIndependentlyVerifiedFromAPS = false
  ; bothIsotopesNotVerifiedByAPS = refl
  ; isotopeIdentityDerivesOpticalTransition = false
  ; isotopeIdentityDoesNotDeriveOpticalTransition = refl
  }

canonicalMountainClockIsNeutral :
  Atomic.Neutral (mountainYb171 canonicalAtomicClockIdentities)
canonicalMountainClockIsNeutral =
  mountainNeutral canonicalAtomicClockIdentities

canonicalCs133RemainsDefiningReference :
  cesiumSecond canonicalAtomicClockIdentities ≡ SI.canonicalCs133SISecondAnchor
canonicalCs133RemainsDefiningReference = refl

------------------------------------------------------------------------
-- 369 constructs are typed *observation indices*. They carry neither
-- calibrated atomic Hamiltonian nor physical field strengths. In particular,
-- a C3 qutrit phase is not a Yb-171 spectroscopy frequency.
------------------------------------------------------------------------

data ObservationKind : Set where
  atomicStateIndex : ObservationKind
  opticalPhaseIndex : ObservationKind
  spacetimeIndex : ObservationKind
  evidenceIndex : ObservationKind

record Indexed369Observation (depth : Nat) : Set where
  field
    kind : ObservationKind
    indexField : Field369.SuperSSP369Field depth
    physicalFieldStrengthDerived : Bool
    noPhysicalFieldStrengthDerived :
      physicalFieldStrengthDerived ≡ false

open Indexed369Observation public

rootAtomicIndex : Indexed369Observation zero
rootAtomicIndex = record
  { kind = atomicStateIndex
  ; indexField = Field369.rootField
  ; physicalFieldStrengthDerived = false
  ; noPhysicalFieldStrengthDerived = refl
  }

fineOpticalIndex : Indexed369Observation (suc (suc (suc zero)))
fineOpticalIndex = record
  { kind = opticalPhaseIndex
  ; indexField = Field369.depth3Field
  ; physicalFieldStrengthDerived = false
  ; noPhysicalFieldStrengthDerived = refl
  }

rootGravityIndex : Indexed369Observation zero
rootGravityIndex = record
  { kind = spacetimeIndex
  ; indexField = Field369.rootField
  ; physicalFieldStrengthDerived = false
  ; noPhysicalFieldStrengthDerived = refl
  }

fineEvidenceIndex : Indexed369Observation (suc (suc (suc zero)))
fineEvidenceIndex = record
  { kind = evidenceIndex
  ; indexField = Field369.depth3Field
  ; physicalFieldStrengthDerived = false
  ; noPhysicalFieldStrengthDerived = refl
  }

------------------------------------------------------------------------
-- Exact 3->6/9->18 refinement square, reused from the existing module.
-- The graph labels resolve bookkeeping; they do NOT split optical Hz into
-- preferred three/six/nine physical states.
------------------------------------------------------------------------

record R2P2ResolutionDiamond : Set where
  field
    three : Refine.Resolution23
    six : Refine.Resolution23
    nine : Refine.Resolution23
    eighteen : Refine.Resolution23

    threeCanonical : three ≡ Refine.phase3Resolution
    sixCanonical : six ≡ Refine.phase6Resolution
    nineCanonical : nine ≡ Refine.phase9Resolution
    eighteenCanonical : eighteen ≡ Refine.phase18Resolution

    viaSix : Refine.ternaryRefine six ≡ eighteen
    viaNine : Refine.binaryRefine nine ≡ eighteen
    refinementCommutes :
      Refine.binaryRefine (Refine.ternaryRefine three)
      ≡ Refine.ternaryRefine (Refine.binaryRefine three)

open R2P2ResolutionDiamond public

canonicalR2P2ResolutionDiamond : R2P2ResolutionDiamond
canonicalR2P2ResolutionDiamond = record
  { three = Refine.phase3Resolution
  ; six = Refine.phase6Resolution
  ; nine = Refine.phase9Resolution
  ; eighteen = Refine.phase18Resolution
  ; threeCanonical = refl
  ; sixCanonical = refl
  ; nineCanonical = refl
  ; eighteenCanonical = refl
  ; viaSix = Refine.phase6-ternary-refines-to-phase18
  ; viaNine = Refine.phase9-binary-refines-to-phase18
  ; refinementCommutes =
      Refine.binary-ternary-refinement-commutes Refine.phase3Resolution
  }

resolutionDiamondAgrees :
  Refine.binaryRefine (Refine.ternaryRefine Refine.phase3Resolution)
  ≡ Refine.ternaryRefine (Refine.binaryRefine Refine.phase3Resolution)
resolutionDiamondAgrees =
  refinementCommutes canonicalR2P2ResolutionDiamond

------------------------------------------------------------------------
-- This causal diamond has five *abstract* events. Its three spatial labels
-- are not three measured clock paths or evidence of 3+1 physical geometry.
------------------------------------------------------------------------

record R2P2FiniteCausalModel : Set where
  field
    finiteChain : Diamond.Chain Diamond.past Diamond.future
    chainDepthTwo :
      Diamond.chainDepth Diamond.past Diamond.future ≡ 2
    antichainWidthThree :
      Diamond.antichainWidth Diamond.past Diamond.future ≡ 3
    rotatedChainDepth :
      Diamond.chainDepth
        (Diamond.transportEvent Diamond.rotateXYZ Diamond.past)
        (Diamond.transportEvent Diamond.rotateXYZ Diamond.future)
      ≡ Diamond.chainDepth Diamond.past Diamond.future
    physicalLorentzMetricMeasuredByDiamond : Bool
    physicalLorentzMetricMeasuredByDiamondIsFalse :
      physicalLorentzMetricMeasuredByDiamond ≡ false

open R2P2FiniteCausalModel public

canonicalR2P2FiniteCausalModel : R2P2FiniteCausalModel
canonicalR2P2FiniteCausalModel = record
  { finiteChain = Diamond.chain-via-x
  ; chainDepthTwo = refl
  ; antichainWidthThree = refl
  ; rotatedChainDepth =
      Diamond.chainDepthInvariant Diamond.rotateXYZ Diamond.past Diamond.future
  ; physicalLorentzMetricMeasuredByDiamond = false
  ; physicalLorentzMetricMeasuredByDiamondIsFalse = refl
  }

------------------------------------------------------------------------
-- Finite qutrit and C3 character structures are existing mathematical
-- test models. They do not assert coherent Yb qutrit control in R2P2.
------------------------------------------------------------------------

record R2P2PhaseIndex : Set where
  field
    finiteQutrit : Qutrit.FiniteQutritWeylCertificate
    qutritIsCanonical :
      finiteQutrit ≡ Qutrit.canonicalFiniteQutritWeylCertificate
    c3Mode : C3.C3CharacterReceipt
    c3ModeIsCanonical : c3Mode ≡ C3.positiveSequenceReceipt
    c3Kernel : Kernel.C3KernelModeReceipt
    c3KernelIsCanonical :
      c3Kernel ≡ Kernel.positiveSequenceKernelReceipt
    physicalOpticalPhaseReadoutDerived : Bool
    noPhysicalOpticalPhaseReadoutDerived :
      physicalOpticalPhaseReadoutDerived ≡ false

open R2P2PhaseIndex public

canonicalR2P2PhaseIndex : R2P2PhaseIndex
canonicalR2P2PhaseIndex = record
  { finiteQutrit = Qutrit.canonicalFiniteQutritWeylCertificate
  ; qutritIsCanonical = refl
  ; c3Mode = C3.positiveSequenceReceipt
  ; c3ModeIsCanonical = refl
  ; c3Kernel = Kernel.positiveSequenceKernelReceipt
  ; c3KernelIsCanonical = refl
  ; physicalOpticalPhaseReadoutDerived = false
  ; noPhysicalOpticalPhaseReadoutDerived = refl
  }

------------------------------------------------------------------------
-- A separate finite quantum-proper-time *candidate* is inherited from an
-- optical-ion-clock source lane. R2P2 neutral-Yb redshift comparison does NOT
-- thereby implement proper-time superposition/interferometry. Physically
-- testing quantumness of gravity needs distinct protocols and observables.
------------------------------------------------------------------------

record QuantumProperTimeComparatorBoundary : Set where
  field
    sourceQuantumModel : Superposition.QuantumClockSuperpositionReceipt
    sourceQuantumModelIsCanonical :
      sourceQuantumModel ≡ Superposition.canonicalQuantumClockSuperpositionReceipt
    r2p2ImplementsQuantumProperTimeSuperposition : Bool
    implementationNotEstablished :
      r2p2ImplementsQuantumProperTimeSuperposition ≡ false
    classicalRedshiftImpliesQuantumGravity : Bool
    noQuantumGravityConsequence :
      classicalRedshiftImpliesQuantumGravity ≡ false

open QuantumProperTimeComparatorBoundary public

canonicalQuantumProperTimeComparatorBoundary :
  QuantumProperTimeComparatorBoundary
canonicalQuantumProperTimeComparatorBoundary = record
  { sourceQuantumModel = Superposition.canonicalQuantumClockSuperpositionReceipt
  ; sourceQuantumModelIsCanonical = refl
  ; r2p2ImplementsQuantumProperTimeSuperposition = false
  ; implementationNotEstablished = refl
  ; classicalRedshiftImpliesQuantumGravity = false
  ; noQuantumGravityConsequence = refl
  }

------------------------------------------------------------------------
-- Optical transfer is explicitly a two-medium, two-way requirement, not an
-- assertion that the link has calibrated reciprocity or a full residual.
------------------------------------------------------------------------

data TransferMedium : Set where
  atmosphericFreeSpace : TransferMedium
  opticalFibre : TransferMedium

data TransferDirection : Set where
  peakToPlains : TransferDirection
  plainsToPeak : TransferDirection

record OpticalTransferLeg : Set where
  field
    medium : TransferMedium
    direction : TransferDirection
    nominalLengthKm : Nat
    reciprocityCalibrated : Bool
    reciprocityCalibratedIsFalse : reciprocityCalibrated ≡ false

open OpticalTransferLeg public

uncalibratedTransferLeg :
  TransferMedium → TransferDirection → Nat → OpticalTransferLeg
uncalibratedTransferLeg path direction length = record
  { medium = path
  ; direction = direction
  ; nominalLengthKm = length
  ; reciprocityCalibrated = false
  ; reciprocityCalibratedIsFalse = refl
  }

-- Four *required* directional contacts, not independently checked links.
-- The APS abstract reports two physical media and full-network shakedown.
-- The video describes optical transfer in both directions, without
-- providing calibrations for each individual directional path.
requiredDirectionalTransferLegs : List OpticalTransferLeg
requiredDirectionalTransferLegs =
  uncalibratedTransferLeg atmosphericFreeSpace peakToPlains 69
  ∷ uncalibratedTransferLeg atmosphericFreeSpace plainsToPeak 69
  ∷ uncalibratedTransferLeg opticalFibre peakToPlains 81
  ∷ uncalibratedTransferLeg opticalFibre plainsToPeak 81
  ∷ []

record R2P2OpticalPhysicsBoundary : Set where
  field
    requiredFourDirectionalLegs : List OpticalTransferLeg
    requiredFourDirectionalLegsAreDeclared :
      requiredFourDirectionalLegs ≡ requiredDirectionalTransferLegs
    vacuumLaw : Optics.KernelLawBridge
    vacuumLawCanonical : vacuumLaw ≡ Optics.maxwellPhaseTransport
    reportedNetwork : R2P2.R2P2PrimarySource
    reportedNetworkIsCanonical :
      reportedNetwork ≡ R2P2.canonicalR2P2PrimarySource
    aboveToothSynthetic : R2P2.AboveCombTooth
    aboveToothIsFiniteExample :
      aboveToothSynthetic ≡ R2P2.exampleAboveCombTooth
    belowToothSynthetic : R2P2.BelowCombTooth
    belowToothIsFiniteExample :
      belowToothSynthetic ≡ R2P2.exampleBelowCombTooth
    twoWayTransferCalibrationDerived : Bool
    noTwoWayTransferCalibrationDerived :
      twoWayTransferCalibrationDerived ≡ false

open R2P2OpticalPhysicsBoundary public

canonicalR2P2OpticalPhysicsBoundary : R2P2OpticalPhysicsBoundary
canonicalR2P2OpticalPhysicsBoundary = record
  { requiredFourDirectionalLegs = requiredDirectionalTransferLegs
  ; requiredFourDirectionalLegsAreDeclared = refl
  ; vacuumLaw = Optics.maxwellPhaseTransport
  ; vacuumLawCanonical = refl
  ; reportedNetwork = R2P2.canonicalR2P2PrimarySource
  ; reportedNetworkIsCanonical = refl
  ; aboveToothSynthetic = R2P2.exampleAboveCombTooth
  ; aboveToothIsFiniteExample = refl
  ; belowToothSynthetic = R2P2.exampleBelowCombTooth
  ; belowToothIsFiniteExample = refl
  ; twoWayTransferCalibrationDerived = false
  ; noTwoWayTransferCalibrationDerived = refl
  }

------------------------------------------------------------------------
-- Convergence of the actual repository owners at a typed architecture.
-- Every external evidence item remains a request. This is not a device
-- construction or a proof of Einstein's equations.
------------------------------------------------------------------------

record R2P2369FullLogicalArchitecture : Set where
  field
    video : R2P2.Veritasium2026Source
    videoCanonical : video ≡ R2P2.canonicalVeritasium2026Source
    sourceBoundary : R2P2.R2P2ClockComparisonBoundary
    sourceBoundaryCanonical :
      sourceBoundary ≡ R2P2.canonicalR2P2ClockComparisonBoundary
    biasIdentifiability : Bias.R2P2BiasIdentifiabilityMaxCut
    biasIdentifiabilityCanonical :
      biasIdentifiability ≡ Bias.canonicalR2P2BiasIdentifiabilityMaxCut
    loopAudit : Loop.ThreeClockLoopSourceBoundary
    loopAuditCanonical : loopAudit ≡ Loop.canonicalThreeClockLoopSourceBoundary
    workflow : ClockPipelinePath
    workflowCanonical : workflow ≡ canonicalClockPipelinePath
    atoms : AtomicClockIdentities
    atomsCanonical : atoms ≡ canonicalAtomicClockIdentities
    lattice : Lattice.OpticalLattice369PhysicalAuthority
    latticeCanonical :
      lattice ≡ Lattice.canonicalOpticalLattice369PhysicalAuthority
    indexedAtomic : Indexed369Observation zero
    indexedAtomicCanonical : indexedAtomic ≡ rootAtomicIndex
    indexedOptical : Indexed369Observation (suc (suc (suc zero)))
    indexedOpticalCanonical : indexedOptical ≡ fineOpticalIndex
    indexedGravity : Indexed369Observation zero
    indexedGravityCanonical : indexedGravity ≡ rootGravityIndex
    indexedEvidence : Indexed369Observation (suc (suc (suc zero)))
    indexedEvidenceCanonical : indexedEvidence ≡ fineEvidenceIndex
    refinement : R2P2ResolutionDiamond
    refinementCanonical : refinement ≡ canonicalR2P2ResolutionDiamond
    causal : R2P2FiniteCausalModel
    causalCanonical : causal ≡ canonicalR2P2FiniteCausalModel
    phase : R2P2PhaseIndex
    phaseCanonical : phase ≡ canonicalR2P2PhaseIndex
    signedBeatWaveCut : WaveCut.WaveCombAuthorityBoundary
    signedBeatWaveCutCanonical :
      signedBeatWaveCut ≡ WaveCut.canonicalWaveCombAuthorityBoundary
    quantumProperTimeComparator : QuantumProperTimeComparatorBoundary
    comparatorCanonical :
      quantumProperTimeComparator ≡ canonicalQuantumProperTimeComparatorBoundary
    optical : R2P2OpticalPhysicsBoundary
    opticalCanonical : optical ≡ canonicalR2P2OpticalPhysicsBoundary
    properTime : Redshift.QuantumClockProperTimeRedshiftBridge
    properTimeCanonical :
      properTime ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    externalMeasurementsIngested : Bool
    measurementsNotIngested :
      externalMeasurementsIngested ≡ false
    fullGRDeviationProved : Bool
    noGRDeviationProof : fullGRDeviationProved ≡ false
    fullQGClaimProved : Bool
    noQGProof : fullQGClaimProved ≡ false
    pendingPhysicalConstruction : List String

open R2P2369FullLogicalArchitecture public

canonicalR2P2369FullLogicalArchitecture : R2P2369FullLogicalArchitecture
canonicalR2P2369FullLogicalArchitecture = record
  { video = R2P2.canonicalVeritasium2026Source
  ; videoCanonical = refl
  ; sourceBoundary = R2P2.canonicalR2P2ClockComparisonBoundary
  ; sourceBoundaryCanonical = refl
  ; biasIdentifiability = Bias.canonicalR2P2BiasIdentifiabilityMaxCut
  ; biasIdentifiabilityCanonical = refl
  ; loopAudit = Loop.canonicalThreeClockLoopSourceBoundary
  ; loopAuditCanonical = refl
  ; workflow = canonicalClockPipelinePath
  ; workflowCanonical = refl
  ; atoms = canonicalAtomicClockIdentities
  ; atomsCanonical = refl
  ; lattice = Lattice.canonicalOpticalLattice369PhysicalAuthority
  ; latticeCanonical = refl
  ; indexedAtomic = rootAtomicIndex
  ; indexedAtomicCanonical = refl
  ; indexedOptical = fineOpticalIndex
  ; indexedOpticalCanonical = refl
  ; indexedGravity = rootGravityIndex
  ; indexedGravityCanonical = refl
  ; indexedEvidence = fineEvidenceIndex
  ; indexedEvidenceCanonical = refl
  ; refinement = canonicalR2P2ResolutionDiamond
  ; refinementCanonical = refl
  ; causal = canonicalR2P2FiniteCausalModel
  ; causalCanonical = refl
  ; phase = canonicalR2P2PhaseIndex
  ; phaseCanonical = refl
  ; signedBeatWaveCut = WaveCut.canonicalWaveCombAuthorityBoundary
  ; signedBeatWaveCutCanonical = refl
  ; quantumProperTimeComparator = canonicalQuantumProperTimeComparatorBoundary
  ; comparatorCanonical = refl
  ; optical = canonicalR2P2OpticalPhysicsBoundary
  ; opticalCanonical = refl
  ; properTime = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; properTimeCanonical = refl
  ; externalMeasurementsIngested = false
  ; measurementsNotIngested = refl
  ; fullGRDeviationProved = false
  ; noGRDeviationProof = refl
  ; fullQGClaimProved = false
  ; noQGProof = refl
  ; pendingPhysicalConstruction =
      "R2P2 neutral-Yb isotope/transition identity must be verified before specific cooling, lattice trapping and interrogation calibration"
      ∷ "two independent optical clocks: systematic shifts, line-shape fits and traceable SI ratios"
      ∷ "comb f_rep and f_CEO, tooth index, signed beat, cycle slips and phase detector"
      ∷ "bidirectional 69 km atmospheric and 81 km fibre link calibration and clocks"
      ∷ "surveyed local geopotential including tides, geodetic datums and worldline convention"
      ∷ "raw time series, uncertainty covariance, fitted fractional shift, blinded comparator and independent replay"
      ∷ "new-physics discriminant beyond a redshift agreement test, if separately justified"
      ∷ []
  }

finiteRefinementConverges :
  refinementCommutes
    (refinement canonicalR2P2369FullLogicalArchitecture)
  ≡ Refine.binary-ternary-refinement-commutes Refine.phase3Resolution
finiteRefinementConverges = refl

fullArchitectureDoesNotProveEinsteinWrong :
  fullGRDeviationProved canonicalR2P2369FullLogicalArchitecture ≡ false
fullArchitectureDoesNotProveEinsteinWrong =
  noGRDeviationProof canonicalR2P2369FullLogicalArchitecture

fullArchitectureDoesNotConstructQuantumGravity :
  fullQGClaimProved canonicalR2P2369FullLogicalArchitecture ≡ false
fullArchitectureDoesNotConstructQuantumGravity =
  noQGProof canonicalR2P2369FullLogicalArchitecture

fullArchitectureDoesNotIngestMeasurements :
  externalMeasurementsIngested canonicalR2P2369FullLogicalArchitecture ≡ false
fullArchitectureDoesNotIngestMeasurements =
  measurementsNotIngested canonicalR2P2369FullLogicalArchitecture

-- A single synthetic height does not identify a slope independently of a
-- nuisance bias. Two selected finite heights separate this candidate pair.
fullArchitectureReusesBiasAmbiguity :
  Bias.syntheticRate Bias.baselineWithLargeBias 3
  ≡ Bias.syntheticRate Bias.doubledSlopeWithSmallBias 3
fullArchitectureReusesBiasAmbiguity =
  Bias.oneHeightCannotDiscriminate

fullArchitectureReusesSecondHeightDiscriminator :
  Bias.syntheticRate Bias.baselineWithLargeBias 9
  ≡ Bias.syntheticRate Bias.doubledSlopeWithSmallBias 9 → Bias.⊥
fullArchitectureReusesSecondHeightDiscriminator =
  Bias.secondHeightDiscriminatesTheseCandidates

-- A third real clock was not introduced by the finite 369 loop construction.
fullArchitectureHasNoObservedTriangle :
  Loop.r2p2ThirdRealClockProvided
    (loopAudit canonicalR2P2369FullLogicalArchitecture) ≡ false
fullArchitectureHasNoObservedTriangle =
  Loop.twoClockR2P2DoesNotSupplyTriangle

fullArchitectureNoCurvatureFromLoopNull :
  Loop.threeClockLoopNullImpliesCurvature
    (loopAudit canonicalR2P2369FullLogicalArchitecture) ≡ false
fullArchitectureNoCurvatureFromLoopNull =
  Loop.threeClockLoopCannotClaimCurvature

------------------------------------------------------------------------
-- Existing 369/wave exact-state witness retained at the TOE root.
-- No 3/6/9 trit rechart can recreate erased signed comb frequency.
------------------------------------------------------------------------

fullArchitectureRetainsSignedBeatInFibre :
  (branch : WaveCut.BeatBranch) →
  SymbolicR2P2.decode
    (SymbolicR2P2.encode WaveCut.signedBeatWaveCoding branch) ≡ branch
fullArchitectureRetainsSignedBeatInFibre =
  WaveCut.signedBeatEncodeDecode

fullArchitectureWaveTruncationCannotDetermineOpticalHz :
  CoreR2P2.ConsumerSufficient
    WaveCut.absoluteBeatOrientation WaveCut.branchOpticalHz → EmptyR2P2.⊥
fullArchitectureWaveTruncationCannotDetermineOpticalHz =
  WaveCut.absoluteBeatTritCannotRecoverOpticalHz

fullArchitectureWaveCutIsNotPhaseCalibration :
  WaveCut.c3ProvesOpticalCarrierPhaseCalibration
    (signedBeatWaveCut canonicalR2P2369FullLogicalArchitecture) ≡ false
fullArchitectureWaveCutIsNotPhaseCalibration =
  WaveCut.waveBridgeDoesNotCalibratePhysicalPhase

------------------------------------------------------------------------
-- Source-distinct 369 atomic optical-lattice control and wave/comb model.
-- A three-site noncommutation witness is NOT the irrational AA transition.
------------------------------------------------------------------------

fullArchitectureFiniteLatticeHoppingDoesNotCommuteWithSitePotential :
  Lattice.nearestNeighbourAdjacency
    (Lattice.siteDependentPotential Lattice.leftBasisState)
    ≡
  Lattice.siteDependentPotential
    (Lattice.nearestNeighbourAdjacency Lattice.leftBasisState)
    →
  EmptyR2P2.⊥
fullArchitectureFiniteLatticeHoppingDoesNotCommuteWithSitePotential =
  Lattice.finiteLatticeOperatorsFailToCommute

fullArchitectureLatticeIsNotInfiniteAAProof :
  Lattice.finiteP3ProvesInfiniteAAThreshold
    (lattice canonicalR2P2369FullLogicalArchitecture) ≡ false
fullArchitectureLatticeIsNotInfiniteAAProof =
  Lattice.latticeCannotProveInfiniteAAThreshold

fullArchitectureDoesNotIdentifyMaStrontiumWithR2P2Ytterbium :
  Lattice.maBichromaticSr87 ≡ Lattice.trianaMountainYb → EmptyR2P2.⊥
fullArchitectureDoesNotIdentifyMaStrontiumWithR2P2Ytterbium =
  Lattice.maIsNotTheR2P2Clock

-- The original Ma 18:11 supercell number and DASHI C18 phase count
-- happen to match as Nat; no carrier/observable map is provided.
fullArchitectureSupercell18NominalCrossProduct :
  Lattice.maFirst813Periods * Lattice.nominal813Nm + 3
  ≡ Lattice.maFirst497Periods * Lattice.nominal497Nm
fullArchitectureSupercell18NominalCrossProduct =
  Lattice.maFirstNominalSupercellOffset

fullArchitectureSupercell18IsNotIdentifiedC18 :
  Lattice.paperSupercell18EqualsPhysicalC18Realization
    (lattice canonicalR2P2369FullLogicalArchitecture) ≡ false
fullArchitectureSupercell18IsNotIdentifiedC18 =
  Lattice.maSupercell18IsNotAnIdentifiedC18PhysicsRealization
