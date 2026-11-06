module DASHI.Biology.Physical.SourceIndexedBiologicalCarrierExact where

------------------------------------------------------------------------
-- P0: FULL COUPLED-CELL CARRIER + HISTORY + OBSERVATION PROVENANCE
--
-- This is a source-constrained *typed integration* of the existing cell
-- carrier and planarian literature observation, not a claim that synthetic
-- Boolean states are measured cell states.  Raw sequence and mechanistic
-- calibration must come from the original DNA/chemical/assay producers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.Cell.CellStateAttractor as Cell
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Finite
import DASHI.Biology.Physical.PlanarianControlCalibrationExact as Planarian

record CoupledBiologicalFrame
    (C : Cell.CoupledCellState) : Set where
  constructor coupledBiologicalFrame
  field
    genome : Cell.GenomeState C
    chromatin : Cell.ChromatinState C
    rna : Cell.RNAState C
    proteome : Cell.ProteomeState C
    metabolism : Cell.MetabolicState C
    membrane : Cell.MembraneState C
    environment : Cell.Environment C
    developmentalHistory : Cell.History C
    assembled : Cell.CellState C
    assembledExactly :
      assembled ≡ Cell.assemble C
        genome chromatin rna proteome metabolism membrane
        environment developmentalHistory
    timeIndex : Nat
    sourceIdentifier : String
    specimenIdentifier : String
    observationProtocol : String

open CoupledBiologicalFrame public

assembleFrame :
  (C : Cell.CoupledCellState) →
  (g : Cell.GenomeState C) →
  (c : Cell.ChromatinState C) →
  (r : Cell.RNAState C) →
  (p : Cell.ProteomeState C) →
  (m : Cell.MetabolicState C) →
  (b : Cell.MembraneState C) →
  (e : Cell.Environment C) →
  (h : Cell.History C) →
  (t : Nat) →
  (source specimen protocol : String) →
  CoupledBiologicalFrame C
assembleFrame C g c r p m b e h t source specimen protocol =
  coupledBiologicalFrame
    g c r p m b e h
    (Cell.assemble C g c r p m b e h) refl
    t source specimen protocol

record SourceQualifiedCellObservation
    (C : Cell.CoupledCellState)
    (Q : Cell.CellPhenotypeQuotient C) : Set where
  constructor sourceQualifiedCellObservation
  field
    frame : CoupledBiologicalFrame C
    observedPhenotype : Cell.Phenotype Q
    matchesNativeObservation :
      observedPhenotype ≡ Cell.phenotype Q (assembled frame)
    observationReceipt : String

open SourceQualifiedCellObservation public

nativeObservation :
  (C : Cell.CoupledCellState)
  (Q : Cell.CellPhenotypeQuotient C)
  (frame : CoupledBiologicalFrame C)
  (receipt : String) →
  SourceQualifiedCellObservation C Q
nativeObservation C Q frame receipt =
  sourceQualifiedCellObservation
    frame (Cell.phenotype Q (assembled frame)) refl receipt

-- History is an actual dynamic coordinate in the finite specialization.
-- The newest action is consed onto the causal history.  This representation
-- is newest-first and must not be mistaken for chronological order in
-- external experiment files.
record FiniteDevelopmentalFrame : Set where
  constructor finiteDevelopmentalFrame
  field
    selectedState : Finite.BiologicalState
    interventionHistory : List Finite.Intervention
    observationTime : Nat
    primarySource : String

open FiniteDevelopmentalFrame public

nextFiniteFrame :
  Finite.Intervention → FiniteDevelopmentalFrame →
  FiniteDevelopmentalFrame
nextFiniteFrame a (finiteDevelopmentalFrame x history t src) =
  finiteDevelopmentalFrame (Finite.step a x) (a ∷ history) (suc t) src

frameHistoryRecordsIntervention :
  (a : Finite.Intervention) (frame : FiniteDevelopmentalFrame) →
  interventionHistory (nextFiniteFrame a frame)
  ≡ a ∷ interventionHistory frame
frameHistoryRecordsIntervention a (finiteDevelopmentalFrame x h t src) = refl

frameTimeAdvances :
  (a : Finite.Intervention) (frame : FiniteDevelopmentalFrame) →
  observationTime (nextFiniteFrame a frame)
  ≡ suc (observationTime frame)
frameTimeAdvances a (finiteDevelopmentalFrame x h t src) = refl

frameStateFollowsNativeFiniteLaw :
  (a : Finite.Intervention) (frame : FiniteDevelopmentalFrame) →
  selectedState (nextFiniteFrame a frame)
  ≡ Finite.step a (selectedState frame)
frameStateFollowsNativeFiniteLaw a (finiteDevelopmentalFrame x h t src) = refl

-- Source-backed *literature observables* are not direct tissue measurements
-- for the finite simulated states.  The exact source counts stay owned by
-- PlanarianControlCalibrationExact and are imported as evidence, not fitted.
record PlanarianOriginalObservationAnchor : Set where
  constructor planarianOriginalObservationAnchor
  field
    parameterSearch : Planarian.CountObservation
    samePublishedParameterSearch :
      parameterSearch ≡ Planarian.hybridModelParameterSweep
    caseIIIFrequencies : Planarian.PercentObservation
    samePublishedFrequencyStatement :
      caseIIIFrequencies ≡ Planarian.caseIIIWildTypeVsSideHead
    publicationReference : String

originalPlanarianLiteratureAnchor : PlanarianOriginalObservationAnchor
originalPlanarianLiteratureAnchor =
  planarianOriginalObservationAnchor
    Planarian.hybridModelParameterSweep refl
    Planarian.caseIIIWildTypeVsSideHead refl
    "Grodstein and Levin (2022), DOI 10.1089/bioe.2021.0036"

-- A source identifier alone never certifies a genotype or a kinetic model.
-- In particular, this file does not attach the 65/35 observations to the
-- synthetic Boolean state dynamics or invent individual treatment records.
