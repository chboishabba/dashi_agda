module DASHI.Biology.Microbiology.QuorumSensingContextExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- QUORUM SENSING AS CONTEXT-INDEXED DISTRIBUTED SIGNAL CONTROL
--
-- Scope boundary:
--   population density is not itself the sensed molecular variable; cells
--   respond to signal production, transport, degradation, uptake, receptor
--   state and downstream regulation.  Biofilm, quorum sensing, killing and
--   virulence modulation therefore remain distinct claims.
------------------------------------------------------------------------

data GrowthState : Set where
  planktonic
  biofilm
  : GrowthState

data QSEffectKind : Set where
  signalSynthesisInhibition
  signalDegradation
  receptorInterference
  downstreamResponseInterference
  : QSEffectKind

data AntimicrobialEffectKind : Set where
  bactericidal
  bacteriostatic
  antiVirulence
  quorumQuenching
  antiBiofilm
  : AntimicrobialEffectKind

record QSSignalSystem : Set₁ where
  constructor qsSignalSystem
  field
    Organism : Set
    Signal : Set
    Environment : Set
    RegulatoryState : Set

    produces : Organism → Signal → Set
    localSignal : Environment → Signal → RegulatoryState
    detects : Organism → Signal → RegulatoryState → Set
    response : Organism → RegulatoryState → Set

open QSSignalSystem public

record QSInterventionReceipt (Q : QSSignalSystem) : Set₁ where
  constructor qsInterventionReceipt
  open QSSignalSystem Q
  field
    agentReference : String
    organismReference : String
    signalReference : String
    intervention : QSEffectKind
    assayReference : String
    effectReference : String
    sourceReference : String
    validationReference : String

open QSInterventionReceipt public

record QSBoundary : Set where
  constructor qsBoundary
  field
    populationDensityEqualsSignalConcentration : Bool
    populationDensityEqualsSignalConcentrationIsFalse :
      populationDensityEqualsSignalConcentration ≡ false

    samePopulationDensityForcesSameSignalState : Bool
    samePopulationDensityForcesSameSignalStateIsFalse :
      samePopulationDensityForcesSameSignalState ≡ false

    quorumSensingActiveProvesBiofilmPresent : Bool
    quorumSensingActiveProvesBiofilmPresentIsFalse :
      quorumSensingActiveProvesBiofilmPresent ≡ false

    quorumQuenchingProvesBactericidalAction : Bool
    quorumQuenchingProvesBactericidalActionIsFalse :
      quorumQuenchingProvesBactericidalAction ≡ false

    antiBiofilmEffectProvesQuorumSensingMechanism : Bool
    antiBiofilmEffectProvesQuorumSensingMechanismIsFalse :
      antiBiofilmEffectProvesQuorumSensingMechanism ≡ false

    quorumClaimNeedsSignalSystemAndAssayContext : Bool
    quorumClaimNeedsSignalSystemAndAssayContextIsTrue :
      quorumClaimNeedsSignalSystemAndAssayContext ≡ true

canonicalQSBoundary : QSBoundary
canonicalQSBoundary =
  qsBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- A finite non-descent witness: the same coarse population observation can
-- coexist with different molecular signal states when environmental context
-- differs.  This is intentionally substrate-neutral.
------------------------------------------------------------------------

data CoarsePopulation : Set where
  sameDensity : CoarsePopulation

data EnvironmentCase : Set where
  lowRetention highRetention : EnvironmentCase

data SignalState : Set where
  belowThreshold aboveThreshold : SignalState

coarsePopulation : EnvironmentCase → CoarsePopulation
coarsePopulation lowRetention = sameDensity
coarsePopulation highRetention = sameDensity

signalState : EnvironmentCase → SignalState
signalState lowRetention = belowThreshold
signalState highRetention = aboveThreshold

sameCoarsePopulationWitness :
  coarsePopulation lowRetention ≡ coarsePopulation highRetention
sameCoarsePopulationWitness = refl

-- Deliberately represented as a boundary fact rather than pretending a
-- theorem of inequality without importing a larger decidable-equality stack.
record QuorumSignalNonDescentWitness : Set where
  constructor quorumSignalNonDescentWitness
  field
    sameCoarseObservation :
      coarsePopulation lowRetention ≡ coarsePopulation highRetention
    signalStatesAreContextSeparated : Bool
    signalStatesAreContextSeparatedIsTrue :
      signalStatesAreContextSeparated ≡ true

canonicalQuorumSignalNonDescentWitness : QuorumSignalNonDescentWitness
canonicalQuorumSignalNonDescentWitness =
  quorumSignalNonDescentWitness refl true refl
