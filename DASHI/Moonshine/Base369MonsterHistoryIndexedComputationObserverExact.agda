module DASHI.Moonshine.Base369MonsterHistoryIndexedComputationObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as B369
import DASHI.Reasoning.HistoryTimeIndexedAlgorithmModelExact as Model

------------------------------------------------------------------------
-- BASE369 / MONSTER AS HISTORY-INDEXED COMPUTATION OBSERVER
--
-- The exact 27-sector carrier is used here as an observer/chart for the role
-- occupied by a computation step.  It is NOT identified with the quantum
-- state, cryptographic secret space, or a Monster representation.
------------------------------------------------------------------------

data ComputationRole : Set where
  observationRole
  candidateRefinementRole
  successfulRecoveryRole
  modelRevisionRole
  : ComputationRole

roleSector : ComputationRole → B369.CubeFrequencySector
roleSector observationRole =
  B369.cubeFrequencySector
    B369.frequencyZero B369.frequencyPositive B369.frequencyZero
roleSector candidateRefinementRole =
  B369.cubeFrequencySector
    B369.frequencyPositive B369.frequencyPositive B369.frequencyZero
roleSector successfulRecoveryRole =
  B369.cubeFrequencySector
    B369.frequencyPositive B369.frequencyNegative B369.frequencyPositive
roleSector modelRevisionRole =
  B369.cubeFrequencySector
    B369.frequencyNegative B369.frequencyZero B369.frequencyPositive

observationAndRecoverySectorsDiffer :
  roleSector observationRole ≡ roleSector successfulRecoveryRole → ⊥
observationAndRecoverySectorsDiffer ()

modelRevisionAndRefinementSectorsDiffer :
  roleSector modelRevisionRole ≡ roleSector candidateRefinementRole → ⊥
modelRevisionAndRefinementSectorsDiffer ()

------------------------------------------------------------------------
-- History/time-indexed chart assignment.
------------------------------------------------------------------------

record HistoryIndexedComputation369Chart
    (surface : Model.HistoryTimeAlgorithmModelSurface) : Set₁ where
  constructor historyIndexedComputation369Chart
  field
    history : Model.History surface
    time : Model.Time surface
    role : ComputationRole
    sector : B369.CubeFrequencySector
    sectorMatchesRole : sector ≡ roleSector role
    modelReference : String
    chartReference : String

open HistoryIndexedComputation369Chart public

record SameOutcomeDifferentComputationHistory : Set₁ where
  constructor sameOutcomeDifferentComputationHistory
  field
    Outcome : Set
    leftOutcome rightOutcome : Outcome
    sameOutcome : leftOutcome ≡ rightOutcome
    leftRole rightRole : ComputationRole
    rolesDiffer : leftRole ≡ rightRole → ⊥
    leftSector rightSector : B369.CubeFrequencySector
    leftSectorExact : leftSector ≡ roleSector leftRole
    rightSectorExact : rightSector ≡ roleSector rightRole
    historyReference : String

open SameOutcomeDifferentComputationHistory public

------------------------------------------------------------------------
-- The exact Base369 facts reused by this observer.
------------------------------------------------------------------------

base369ComputationChartHasTwentySevenSectorLabels :
  B369.cubeSectorCount ≡ 27
base369ComputationChartHasTwentySevenSectorLabels = B369.cubeSectorCountIs27

base369ConjugationIsInvolutive :
  (sector : B369.CubeFrequencySector) →
  B369.conjugateCubeSector (B369.conjugateCubeSector sector) ≡ sector
base369ConjugationIsInvolutive = B369.cubeSectorConjugationInvolutive

monsterP3AnchorRemainsNeutralOrigin :
  B369.monsterP3AxisAnchor ≡ B369.Geometry.origin
monsterP3AnchorRemainsNeutralOrigin = B369.monsterP3AxisAnchorIsOrigin

------------------------------------------------------------------------
-- Boundary: a useful 369 chart / Monster intertwiner does not become authority
-- for quantum speedup, cryptographic recovery, or representation identity.
------------------------------------------------------------------------

record Base369MonsterComputationObserverBoundary : Set where
  constructor base369MonsterComputationObserverBoundary
  field
    base369MayIndexComputationRoles : Bool
    base369MayIndexComputationRolesIsTrue :
      base369MayIndexComputationRoles ≡ true
    sameFinalOutcomeImpliesSameComputationRole : Bool
    sameFinalOutcomeImpliesSameComputationRoleIsFalse :
      sameFinalOutcomeImpliesSameComputationRole ≡ false
    sectorLabelProvesCryptographicSecretRecovery : Bool
    sectorLabelProvesCryptographicSecretRecoveryIsFalse :
      sectorLabelProvesCryptographicSecretRecovery ≡ false
    sectorLabelProvesQuantumSpeedup : Bool
    sectorLabelProvesQuantumSpeedupIsFalse :
      sectorLabelProvesQuantumSpeedup ≡ false
    base369CubeIsMonsterRepresentation : Bool
    base369CubeIsMonsterRepresentationIsFalse :
      base369CubeIsMonsterRepresentation ≡ false
    monsterIntertwinerMakesQuantumCryptoMonsterPhysical : Bool
    monsterIntertwinerMakesQuantumCryptoMonsterPhysicalIsFalse :
      monsterIntertwinerMakesQuantumCryptoMonsterPhysical ≡ false

canonicalBase369MonsterComputationObserverBoundary :
  Base369MonsterComputationObserverBoundary
canonicalBase369MonsterComputationObserverBoundary =
  base369MonsterComputationObserverBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
