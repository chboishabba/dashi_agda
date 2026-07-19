module DASHI.Physics.Chemistry.AtomicPeriodicTableRecoveryBoundary where

open import DASHI.Physics.Chemistry.AtomicForceSectorSeparation
open import DASHI.Physics.Chemistry.AtomicOrbitDiameterControl
open import DASHI.Physics.Chemistry.AtomicShellRecurrence

-- This record is the narrow theorem boundary for periodic-table recovery.
-- Each physical bridge is supplied independently; the record does not promote
-- a pre-spectral force observable into an orbital spectrum.
record AtomicPeriodicTableRecoveryBoundary : Set₁ where
  field
    forceSectors       : AtomicForceSectorSeparation
    orbitControl       : AtomicOrbitDiameterControl
    shellRecurrence    : AtomicShellRecurrence

    MassScaleSeparated : Set
    DiameterSeparated  : Set
    CentralFieldLimit  : Set
    FermionicLift      : Set
    InteractingMinimum : Set
    ShellDictionary    : Set
    ValenceProjection  : Set

    massScaleWitness   : MassScaleSeparated
    diameterWitness    : DiameterSeparated
    centralFieldWitness : CentralFieldLimit
    fermionicWitness   : FermionicLift
    interactingMinimumWitness : InteractingMinimum
    shellDictionaryWitness : ShellDictionary
    valenceProjectionWitness : ValenceProjection

-- What can be claimed once every bridge witness is present.
record PeriodicTableRecoveryWitness
  (B : AtomicPeriodicTableRecoveryBoundary) : Set₁ where
  open AtomicPeriodicTableRecoveryBoundary B
  field
    OrbitSpectrumRecovered : Set
    ShellStructureRecovered : Set
    PeriodicValenceRecovered : Set

    orbitSpectrumRecovered : OrbitSpectrumRecovered
    shellStructureRecovered : ShellStructureRecovered
    periodicValenceRecovered : PeriodicValenceRecovered

-- Explicit blocker surface.  A repository consumer can expose this record
-- without claiming the final recovery witness exists.
record AtomicPeriodicTableOpenObligations
  (B : AtomicPeriodicTableRecoveryBoundary) : Set₁ where
  field
    maxwellToCentralPotential : Set
    operatorToOrbitSpectrum   : Set
    antisymmetryToOccupation  : Set
    selfConsistentGroundState : Set
    spectralGapToShellLock    : Set
    shellClosureToValenceRecurrence : Set

-- The assembly theorem is intentionally structural: a completed witness is
-- consumable as a periodic-table recovery witness, but is never manufactured
-- from the boundary record alone.
periodicTableRecoveryAvailable :
  {B : AtomicPeriodicTableRecoveryBoundary} →
  PeriodicTableRecoveryWitness B →
  PeriodicTableRecoveryWitness B
periodicTableRecoveryAvailable witness = witness
