module DASHI.Biology.Physical.DNAChemistryRegulatoryOperatorBridgeExact where

------------------------------------------------------------------------
-- Existing-owner bridge:
--
--   DNA sequence -> chemistry/constraint energy -> context-sensitive
--   regulatory parameter -> cell-state update.
--
-- This reuses DNAChemistryEnergyAlgebra rather than introducing a second DNA
-- energy ontology.  The finite model below is an operational regression, not a
-- microscopic quantum-chemistry or calibrated gene-regulation model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List.Base using (List; []; _∷_)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.DNAChemistryEnergyAlgebra as Energy

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- A nontrivial exact operational energy model over the existing owner.
------------------------------------------------------------------------

unitWeights : Energy.EnergyWeights
unitWeights = Energy.weights 1 0 0 0 0 0 0

exactGC : List DNA.DNABase → Energy.ExactConstraintEnergy
exactGC xs = Energy.exactEnergy (Energy.gcCount xs) 0 0

zeroThermo : List DNA.DNABase → Energy.OperationalThermoEnergy
zeroThermo xs = Energy.thermoEnergy 0 0 0 0

gcOperationalModel : Energy.OperationalChemistryModel
gcOperationalModel = Energy.model exactGC zeroThermo unitWeights

atSequence gcSequence : List DNA.DNABase
atSequence = DNA.A ∷ DNA.T ∷ []
gcSequence = DNA.G ∷ DNA.C ∷ []

atEnergyIsZero : Energy.Hamiltonian gcOperationalModel atSequence ≡ 0
atEnergyIsZero = refl

gcEnergyIsTwo : Energy.Hamiltonian gcOperationalModel gcSequence ≡ 2
gcEnergyIsTwo = refl

------------------------------------------------------------------------
-- Energy does not directly mean expression.  Context participates in the
-- parameter compiler, as demanded by the physical-development lane.
------------------------------------------------------------------------

data Accessibility : Set where
  closed openState : Accessibility

data RegulatoryParameter : Set where
  lowExpression highExpression : RegulatoryParameter

compileRegulatoryParameter :
  Accessibility → Nat → RegulatoryParameter
compileRegulatoryParameter closed energy = lowExpression
compileRegulatoryParameter openState 0 = lowExpression
compileRegulatoryParameter openState (suc energy) = highExpression

sameSequenceDifferentAccessibilityChangesRegulation :
  compileRegulatoryParameter closed (Energy.Hamiltonian gcOperationalModel gcSequence)
  ≢
  compileRegulatoryParameter openState (Energy.Hamiltonian gcOperationalModel gcSequence)
sameSequenceDifferentAccessibilityChangesRegulation ()

record RegulatoryCellState : Set where
  constructor regulatoryCellState
  field
    channelHigh : Bool

open RegulatoryCellState public

applyRegulatoryParameter : RegulatoryParameter → RegulatoryCellState → RegulatoryCellState
applyRegulatoryParameter lowExpression state = regulatoryCellState false
applyRegulatoryParameter highExpression state = regulatoryCellState true

regulatoryUpdate :
  Accessibility → List DNA.DNABase → RegulatoryCellState → RegulatoryCellState
regulatoryUpdate context sequence state =
  applyRegulatoryParameter
    (compileRegulatoryParameter context (Energy.Hamiltonian gcOperationalModel sequence))
    state

sameDNAEnergyDifferentContextChangesCellParameter :
  channelHigh (regulatoryUpdate closed gcSequence (regulatoryCellState false))
  ≢
  channelHigh (regulatoryUpdate openState gcSequence (regulatoryCellState false))
sameDNAEnergyDifferentContextChangesCellParameter ()

------------------------------------------------------------------------
-- Existing authority boundary preserved.
------------------------------------------------------------------------

record DNAEnergyRegulatoryBoundary : Set where
  field
    operationalEnergyIsCompleteQuantumHamiltonian : Bool
    operationalEnergyIsCompleteQuantumHamiltonianIsFalse :
      operationalEnergyIsCompleteQuantumHamiltonian ≡ false
    energyAloneDeterminesExpression : Bool
    energyAloneDeterminesExpressionIsFalse :
      energyAloneDeterminesExpression ≡ false

canonicalDNAEnergyRegulatoryBoundary : DNAEnergyRegulatoryBoundary
canonicalDNAEnergyRegulatoryBoundary = record
  { operationalEnergyIsCompleteQuantumHamiltonian = false
  ; operationalEnergyIsCompleteQuantumHamiltonianIsFalse = refl
  ; energyAloneDeterminesExpression = false
  ; energyAloneDeterminesExpressionIsFalse = refl
  }
