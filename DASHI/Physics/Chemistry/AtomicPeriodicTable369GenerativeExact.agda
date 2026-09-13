module DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Physics.Foundations.AtomicFermionShellExact as Atomic
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as Valence
import DASHI.Physics.Chemistry.AtomicShellRecurrence as Recurrence
import DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary as Recovery

------------------------------------------------------------------------
-- Purpose
--
-- Canonical generative owner for the atom/periodic-table formalism recovered
-- from the historical DASHI Atom thread and welded to the current repo-native
-- 369, fermion, valence, shell-recurrence, and recovery owners.
--
-- The construction is deliberately staged:
--
--   369/ternary substrate
--     -> physical representation
--     -> one-particle modes
--     -> antisymmetric many-fermion state
--     -> interacting energy / ground-state selection
--     -> shell occupancy
--     -> energetic valence quotient
--     -> shell-completion recurrence
--     -> periodic-table observable quotient.
--
-- This file does not promote triadic cardinality into orbital quantum numbers,
-- a supplied filling order into a Hamiltonian theorem, or a structural closure
-- into empirical spectra / ionisation / bonding / nuclear-stability claims.

------------------------------------------------------------------------
-- 1. Existing 369 substrate is reused, not redefined.

TernaryKernel : Nat -> Set
TernaryKernel = Triadic.Kernel

NineSheet : Set
NineSheet = Triadic.NineSheet

nineSheetLift : {d : Nat} -> TernaryKernel d -> NineSheet -> TernaryKernel (suc (suc d))
nineSheetLift = Triadic.liftNine

nineSheetLiftRoundTrip :
  {d : Nat} (xs : TernaryKernel d) (sheet : NineSheet) ->
  Triadic.splitNine (nineSheetLift xs sheet) ≡ (xs , sheet)
nineSheetLiftRoundTrip = Triadic.splitLiftNine

------------------------------------------------------------------------
-- 2. Atomic identity is indexed independently from electronic configuration.

record AtomicIndex : Set where
  constructor atomicIndex
  field
    protonNumber : Nat
    neutronNumber : Nat
    electronNumber : Nat

open AtomicIndex public

Neutral : AtomicIndex -> Set
Neutral a = electronNumber a ≡ protonNumber a

ElementEquivalent : AtomicIndex -> AtomicIndex -> Set
ElementEquivalent a b = protonNumber a ≡ protonNumber b

IsotopeEquivalent : AtomicIndex -> AtomicIndex -> Set
IsotopeEquivalent a b =
  protonNumber a ≡ protonNumber b × neutronNumber a ≡ neutronNumber b

neutralAt : (z n : Nat) -> AtomicIndex
neutralAt z n = atomicIndex z n z

neutralAtIsNeutral : (z n : Nat) -> Neutral (neutralAt z n)
neutralAtIsNeutral z n = refl

------------------------------------------------------------------------
-- 3. One-particle representation / shell capacities.
--
-- Orbital labels remain imported physical-representation data.  Once supplied,
-- the capacity consequences are exact combinatorics.

OrbitalLabel : Set
OrbitalLabel = Atomic.OrbitalLabel

subshellCapacity : Nat -> Nat
subshellCapacity = Atomic.subshellCapacity

shellCapacity : Nat -> Nat
shellCapacity = Atomic.shellCapacity

sCapacity : subshellCapacity 0 ≡ 2
sCapacity = Atomic.sSubshellCapacityIsTwo

pCapacity : subshellCapacity 1 ≡ 6
pCapacity = Atomic.pSubshellCapacityIsSix

dCapacity : subshellCapacity 2 ≡ 10
dCapacity = Atomic.dSubshellCapacityIsTen

firstShellCapacity : shellCapacity 1 ≡ 2
firstShellCapacity = Atomic.firstShellCapacityIsTwo

secondShellCapacity : shellCapacity 2 ≡ 8
secondShellCapacity = Atomic.secondShellCapacityIsEight

thirdShellCapacity : shellCapacity 3 ≡ 18
thirdShellCapacity = Atomic.thirdShellCapacityIsEighteen

------------------------------------------------------------------------
-- 4. Fermionic occupation / exclusion is more than a bare capacity count.

FermionLabel : Set
FermionLabel = Valence.FermionLabel

ExteriorOccupancyStatus : Set
ExteriorOccupancyStatus = Valence.ExteriorOccupancyStatus

duplicateStateVanishes :
  Valence.exteriorStatus Valence.fermionAlpha Valence.fermionAlpha
  ≡ Valence.duplicateOneParticleStateVanishing
duplicateStateVanishes = Valence.duplicateAlphaStateVanishes

mixedStateAllowed :
  Valence.exteriorStatus Valence.fermionAlpha Valence.fermionBeta
  ≡ Valence.exteriorStateAllowed
mixedStateAllowed = Valence.mixedPairIsAllowed

------------------------------------------------------------------------
-- 5. Typed generation stages.

data GenerationStage : Set where
  ternarySubstrateStage : GenerationStage
  physicalRealizationStage : GenerationStage
  nuclearChargeStage : GenerationStage
  nuclearStabilityStage : GenerationStage
  oneParticleRepresentationStage : GenerationStage
  antisymmetricManyElectronStage : GenerationStage
  interactingEnergyStage : GenerationStage
  groundStateSelectionStage : GenerationStage
  shellOccupancyStage : GenerationStage
  valenceProjectionStage : GenerationStage
  shellRecurrenceStage : GenerationStage
  observableChemistryStage : GenerationStage

data DependsOn : GenerationStage -> GenerationStage -> Set where
  realizationNeedsSubstrate : DependsOn physicalRealizationStage ternarySubstrateStage
  nuclearStabilityNeedsCharge : DependsOn nuclearStabilityStage nuclearChargeStage
  oneParticleNeedsRealization : DependsOn oneParticleRepresentationStage physicalRealizationStage
  antisymmetryNeedsOneParticle : DependsOn antisymmetricManyElectronStage oneParticleRepresentationStage
  energyNeedsAntisymmetry : DependsOn interactingEnergyStage antisymmetricManyElectronStage
  groundNeedsEnergy : DependsOn groundStateSelectionStage interactingEnergyStage
  shellNeedsGround : DependsOn shellOccupancyStage groundStateSelectionStage
  valenceNeedsShell : DependsOn valenceProjectionStage shellOccupancyStage
  recurrenceNeedsValence : DependsOn shellRecurrenceStage valenceProjectionStage
  observableNeedsRecurrence : DependsOn observableChemistryStage shellRecurrenceStage

------------------------------------------------------------------------
-- 6. Consumer-relative generative formalism.
--
-- We keep the physical carriers abstract so this owner can compose the repo's
-- exact finite structural theorems without fabricating an unproved continuum
-- Hamiltonian or empirical calibration.

record AtomicGenerator : Set₁ where
  field
    PhysicalRealization : Set
    OneParticleState : Set
    ManyElectronState : Set
    InteractingEnergy : Set
    GroundConfiguration : Set
    ShellState : Set
    ValenceState : Set
    ChemistryObservable : Set

    realize : (d : Nat) -> TernaryKernel d -> PhysicalRealization
    oneParticle : PhysicalRealization -> OneParticleState
    antisymmetrize : Nat -> OneParticleState -> ManyElectronState
    interactingEnergy : AtomicIndex -> ManyElectronState -> InteractingEnergy
    selectGround : AtomicIndex -> InteractingEnergy -> GroundConfiguration
    shellOf : GroundConfiguration -> ShellState
    valenceOf : GroundConfiguration -> ValenceState
    observeChemistry : ValenceState -> ChemistryObservable

------------------------------------------------------------------------
-- 7. Periodicity is recurrence under shell completion, not one global period.

record PeriodicValenceStructure (G : AtomicGenerator) : Set₁ where
  open AtomicGenerator G
  field
    CompletionStep : GroundConfiguration -> GroundConfiguration -> Set
    ShellClosed : GroundConfiguration -> Set
    ValenceEquivalent : ValenceState -> ValenceState -> Set

    completionPreservesPeriodicClass :
      {x y : GroundConfiguration} ->
      CompletionStep x y ->
      ShellClosed x ->
      ValenceEquivalent (valenceOf x) (valenceOf y)

------------------------------------------------------------------------
-- 8. Periodic table as an ordered observable quotient of generated atoms.

record GeneratedAtom (G : AtomicGenerator) : Set where
  open AtomicGenerator G
  constructor generatedAtom
  field
    index : AtomicIndex
    ground : GroundConfiguration
    shell : ShellState
    valence : ValenceState
    observable : ChemistryObservable

record PeriodicObservation (G : AtomicGenerator) : Set₁ where
  open AtomicGenerator G
  field
    PeriodClass : Set
    observePeriodClass : GeneratedAtom G -> PeriodClass

  _≈periodic_ : GeneratedAtom G -> GeneratedAtom G -> Set
  a ≈periodic b = observePeriodClass a ≡ observePeriodClass b

------------------------------------------------------------------------
-- 9. Explicit end-to-end constructor contract.

record ElementConstructor (G : AtomicGenerator) : Set₁ where
  open AtomicGenerator G
  field
    chooseNeutrons : Nat -> Nat
    physicalInput : (z : Nat) -> PhysicalRealization
    oneParticleInput : (z : Nat) -> OneParticleState
    manyElectronInput : (z : Nat) -> ManyElectronState
    energyInput : (z : Nat) -> InteractingEnergy
    groundInput : (z : Nat) -> GroundConfiguration

    physicalInputIsRealized :
      (z : Nat) -> oneParticle (physicalInput z) ≡ oneParticleInput z

    manyElectronInputIsAntisymmetric :
      (z : Nat) -> antisymmetrize z (oneParticleInput z) ≡ manyElectronInput z

    energyInputIsInteracting :
      (z : Nat) ->
      interactingEnergy (neutralAt z (chooseNeutrons z)) (manyElectronInput z)
      ≡ energyInput z

    groundInputIsSelected :
      (z : Nat) ->
      selectGround (neutralAt z (chooseNeutrons z)) (energyInput z)
      ≡ groundInput z

  element : Nat -> GeneratedAtom G
  element z =
    generatedAtom
      (neutralAt z (chooseNeutrons z))
      (groundInput z)
      (shellOf (groundInput z))
      (valenceOf (groundInput z))
      (observeChemistry (valenceOf (groundInput z)))

------------------------------------------------------------------------
-- 10. Archive-regression closure coordinates.
--
-- The historical atom thread reports the finite MDL filling experiment as
-- producing helium-/neon-/argon-like closure points 2, 10, 18.  These are kept
-- as regression coordinates, not promoted to a complete empirical theorem.

data HistoricalClosureClass : Set where
  heliumLikeClosure : HistoricalClosureClass
  neonLikeClosure : HistoricalClosureClass
  argonLikeClosure : HistoricalClosureClass

historicalClosureZ : HistoricalClosureClass -> Nat
historicalClosureZ heliumLikeClosure = 2
historicalClosureZ neonLikeClosure = 10
historicalClosureZ argonLikeClosure = 18

heliumLikeZ : historicalClosureZ heliumLikeClosure ≡ 2
heliumLikeZ = refl

neonLikeZ : historicalClosureZ neonLikeClosure ≡ 10
neonLikeZ = refl

argonLikeZ : historicalClosureZ argonLikeClosure ≡ 18
argonLikeZ = refl

------------------------------------------------------------------------
-- 11. Reuse existing valence quotient language.

ValencePattern : Set
ValencePattern = Valence.ValencePattern

ValenceClass : Set
ValenceClass = Valence.ValenceEquivalenceClass

valenceClass : ValencePattern -> ValenceClass
valenceClass = Valence.valenceClass

closedValenceIsNobleLike :
  valenceClass Valence.closedValencePattern ≡ Valence.nobleLikeClass
closedValenceIsNobleLike = refl

sameClassCanHaveDifferentRepresentatives :
  valenceClass Valence.twoActivePStates
  ≡ valenceClass Valence.sixActivePStates
sameClassCanHaveDifferentRepresentatives =
  Valence.sameClassAcrossDifferentValenceRepresentatives

------------------------------------------------------------------------
-- 12. Existing shell-recurrence and recovery owners are explicit dependencies.

ExistingShellRecurrence : Set₁
ExistingShellRecurrence = Recurrence.AtomicShellRecurrence

ExistingPeriodicTableRecoveryBoundary : Set₁
ExistingPeriodicTableRecoveryBoundary = Recovery.AtomicPeriodicTableRecoveryBoundary

ExistingPeriodicTableRecoveryWitness :
  ExistingPeriodicTableRecoveryBoundary -> Set₁
ExistingPeriodicTableRecoveryWitness = Recovery.PeriodicTableRecoveryWitness

------------------------------------------------------------------------
-- 13. Full recovery contract.
--
-- A physical periodic-table claim is stronger than structural generation.
-- Each bridge is separately named so later proofs can discharge exactly the
-- missing consumer rather than smuggling authority through a constructor.

record FullPeriodicTableRecovery (G : AtomicGenerator) : Set₁ where
  open AtomicGenerator G
  field
    SpectrumRecovery : Set
    ShellRecovery : Set
    FermionicOccupationRecovery : Set
    GroundStateRecovery : Set
    ValenceRecovery : Set
    ValenceRecurrenceRecovery : Set
    ObservableCompatibility : Set
    NuclearStabilityCompatibility : Set

    spectrumRecovery : SpectrumRecovery
    shellRecovery : ShellRecovery
    fermionicOccupationRecovery : FermionicOccupationRecovery
    groundStateRecovery : GroundStateRecovery
    valenceRecovery : ValenceRecovery
    valenceRecurrenceRecovery : ValenceRecurrenceRecovery
    observableCompatibility : ObservableCompatibility
    nuclearStabilityCompatibility : NuclearStabilityCompatibility

------------------------------------------------------------------------
-- 14. Non-promotion firewall.

record Atomic369NonPromotionBoundary : Set where
  constructor atomic369NonPromotionBoundary
  field
    triadicCardinalityDerivesOrbitalQuantumNumbers : Bool
    triadicCardinalityDerivesOrbitalQuantumNumbersIsFalse :
      triadicCardinalityDerivesOrbitalQuantumNumbers ≡ false

    shellCapacityDeterminesPhysicalEnergyOrdering : Bool
    shellCapacityDeterminesPhysicalEnergyOrderingIsFalse :
      shellCapacityDeterminesPhysicalEnergyOrdering ≡ false

    protonNumberAloneProvesNuclearStability : Bool
    protonNumberAloneProvesNuclearStabilityIsFalse :
      protonNumberAloneProvesNuclearStability ≡ false

    structuralClosureProvesEmpiricalSpectrum : Bool
    structuralClosureProvesEmpiricalSpectrumIsFalse :
      structuralClosureProvesEmpiricalSpectrum ≡ false

    finiteClosureRegressionProvesFullPeriodicTable : Bool
    finiteClosureRegressionProvesFullPeriodicTableIsFalse :
      finiteClosureRegressionProvesFullPeriodicTable ≡ false

    elementCountFollowsFromNineSheetCardinality : Bool
    elementCountFollowsFromNineSheetCardinalityIsFalse :
      elementCountFollowsFromNineSheetCardinality ≡ false

canonicalAtomic369NonPromotionBoundary : Atomic369NonPromotionBoundary
canonicalAtomic369NonPromotionBoundary =
  atomic369NonPromotionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- 15. Canonical statement exposed to downstream consumers.
--
-- Geometry/algebra supplies an admissible structural carrier; fermionic and
-- energetic dynamics select an atom; valence recurrence supplies periodicity.
-- The final empirical recovery remains a separate typed contract.

record CanonicalAtomicPeriodicTableStatement : Set₁ where
  field
    Generator : AtomicGenerator
    periodicValence : PeriodicValenceStructure Generator
    constructor : ElementConstructor Generator
    observation : PeriodicObservation Generator
    nonPromotion : Atomic369NonPromotionBoundary

  generatedElement : Nat -> GeneratedAtom Generator
  generatedElement = ElementConstructor.element constructor
