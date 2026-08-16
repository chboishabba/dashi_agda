module DASHI.Biology.Physical.IteratedAttractorScaleLiftExact where

------------------------------------------------------------------------
-- Iterated attractors across biological scales.
--
-- A stable lower-scale regime can be observed as one effective state at the
-- next scale.  This module proves a finite compositional example; it does not
-- claim a universal renormalization theorem for biology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Molecular scale: two microstates repair to one stable cellular regime.
------------------------------------------------------------------------

data MolecularState : Set where
  damagedProtein functionalProtein : MolecularState

molecularRepair : MolecularState → MolecularState
molecularRepair damagedProtein = functionalProtein
molecularRepair functionalProtein = functionalProtein

molecularRepairIdempotent :
  (x : MolecularState) → molecularRepair (molecularRepair x) ≡ molecularRepair x
molecularRepairIdempotent damagedProtein = refl
molecularRepairIdempotent functionalProtein = refl

data CellularRegime : Set where
  lowFunction highFunction : CellularRegime

observeCell : MolecularState → CellularRegime
observeCell damagedProtein = lowFunction
observeCell functionalProtein = highFunction

molecularAttractorLiftsToHighCellRegime :
  (x : MolecularState) → observeCell (molecularRepair x) ≡ highFunction
molecularAttractorLiftsToHighCellRegime damagedProtein = refl
molecularAttractorLiftsToHighCellRegime functionalProtein = refl

------------------------------------------------------------------------
-- Cellular scale: the effective cellular regime becomes input to a tissue
-- repair map whose attractor is then observed at organ scale.
------------------------------------------------------------------------

data TissueState : Set where
  disconnected connected : TissueState

cellToTissueDrive : CellularRegime → TissueState → TissueState
cellToTissueDrive lowFunction tissue = tissue
cellToTissueDrive highFunction disconnected = connected
cellToTissueDrive highFunction connected = connected

highCellRegimeStabilizesConnectedTissue :
  (x : TissueState) →
  cellToTissueDrive highFunction
    (cellToTissueDrive highFunction x)
  ≡ cellToTissueDrive highFunction x
highCellRegimeStabilizesConnectedTissue disconnected = refl
highCellRegimeStabilizesConnectedTissue connected = refl

data OrganRegime : Set where
  incompleteOrgan integratedOrgan : OrganRegime

observeOrgan : TissueState → OrganRegime
observeOrgan disconnected = incompleteOrgan
observeOrgan connected = integratedOrgan

------------------------------------------------------------------------
-- Composed scale-lift theorem.
------------------------------------------------------------------------

multiscaleRepair : MolecularState → TissueState → OrganRegime
multiscaleRepair molecular tissue =
  observeOrgan
    (cellToTissueDrive
      (observeCell (molecularRepair molecular))
      tissue)

multiscaleRepairReachesIntegratedOrgan :
  (molecular : MolecularState) (tissue : TissueState) →
  multiscaleRepair molecular tissue ≡ integratedOrgan
multiscaleRepairReachesIntegratedOrgan damagedProtein disconnected = refl
multiscaleRepairReachesIntegratedOrgan damagedProtein connected = refl
multiscaleRepairReachesIntegratedOrgan functionalProtein disconnected = refl
multiscaleRepairReachesIntegratedOrgan functionalProtein connected = refl

-- The important direction is compositional:
-- lower-scale attractor -> effective coarse state -> higher-scale attractor.
-- No converse claim says the higher-scale goal uniquely determines a microstate.
