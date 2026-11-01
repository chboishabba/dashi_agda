module DASHI.Biology.Cell.BioelectricNetwork where

-- Bioelectric state is a cell/tissue-scale control carrier, distinct from the
-- atomic electromagnetic sector that supplies chemistry.
record BioelectricNetwork : Set₁ where
  field
    Node          : Set
    Voltage       : Set
    Conductance   : Set
    Current       : Set
    ChannelState  : Set
    GapJunctionState : Set
    ChemicalSignal : Set
    MechanicalState : Set
    RegulatoryState : Set
    NetworkState  : Set
    Environment   : Set

    voltageAt     : NetworkState → Node → Voltage
    coupling      : NetworkState → Node → Node → Conductance
    ionicCurrent  : NetworkState → Node → Current
    channelState  : NetworkState → Node → ChannelState
    gapJunction   : NetworkState → Node → Node → GapJunctionState

    update :
      Environment → ChemicalSignal → MechanicalState → RegulatoryState →
      NetworkState → NetworkState

record BioelectricPatternProjection
  (B : BioelectricNetwork) : Set₁ where
  open BioelectricNetwork B
  field
    Pattern     : Set
    GoalPattern : Set

    observePattern : NetworkState → Pattern
    decodeGoal     : Pattern → GoalPattern

    SamePattern : NetworkState → NetworkState → Set
    SameGoal    : NetworkState → NetworkState → Set

record BioelectricPatternMemoryWitness
  {B : BioelectricNetwork}
  (P : BioelectricPatternProjection B) : Set₁ where
  open BioelectricNetwork B
  open BioelectricPatternProjection P
  field
    Perturbation : Set
    perturb      : Perturbation → NetworkState → NetworkState
    repair       : GoalPattern → NetworkState → NetworkState

    initial      : NetworkState
    perturbation : Perturbation

    latentGoalPreserved :
      SameGoal initial (perturb perturbation initial)

    triggeredRestoration :
      SameGoal initial
        (repair (decodeGoal (observePattern initial))
          (perturb perturbation initial))

-- Morphogenesis requires coupled chemical, mechanical, regulatory, and
-- bioelectric witnesses; voltage is not installed as a sole master code.
record CoupledBioelectricMorphogenesis
  (B : BioelectricNetwork) : Set₁ where
  open BioelectricNetwork B
  field
    ChemicalCouplingRecovered : Set
    MechanicalCouplingRecovered : Set
    RegulatoryCouplingRecovered : Set
    GapJunctionCouplingRecovered : Set

    chemicalWitness : ChemicalCouplingRecovered
    mechanicalWitness : MechanicalCouplingRecovered
    regulatoryWitness : RegulatoryCouplingRecovered
    gapJunctionWitness : GapJunctionCouplingRecovered

record BioelectricAuthorityBoundary : Set₁ where
  field
    voltagePatternIsNotMemoryByDefinition : Set
    attractorIsNotRepresentationByDefinition : Set
    bioelectricityIsNotSoleMorphogeneticCause : Set
    competenceIsNotConsciousness : Set
    animalRepairIsNotHumanClinicalAuthority : Set
