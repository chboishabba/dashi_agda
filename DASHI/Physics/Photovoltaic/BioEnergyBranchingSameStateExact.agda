module DASHI.Physics.Photovoltaic.BioEnergyBranchingSameStateExact where

-- Mechanism-first BH4-derived photovoltaic BIOENGINEERING, 2026-11-16.
-- A deliberately finite source-compatible bookkeeping interface.
-- None of the numerical witness values is a measured living organism.
-- Native Agda compiler validation remains OPEN.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

record PhotosystemWindow : Set where
  constructor photosystemWindow
  field
    incidentPhotonQuanta escapedPhotonQuanta absorbedPhotonQuanta : Nat
    incidentPartition : incidentPhotonQuanta ≡ absorbedPhotonQuanta + escapedPhotonQuanta

    separatedElectronQuanta fluorescenceQuanta nonradiativeQuanta : Nat
    absorbedPartition :
      absorbedPhotonQuanta ≡
      separatedElectronQuanta + (fluorescenceQuanta + nonradiativeQuanta)

    transferredElectronQuanta recombinedQuanta : Nat
    chargeSeparationPartition :
      separatedElectronQuanta ≡ transferredElectronQuanta + recombinedQuanta

    extracellularElectronQuanta carbonElectronQuanta respirationElectronQuanta : Nat
    fuelElectronQuanta reactiveOxygenElectronQuanta : Nat
    electronAllocation :
      transferredElectronQuanta ≡
      extracellularElectronQuanta +
        (carbonElectronQuanta +
        (respirationElectronQuanta +
        (fuelElectronQuanta + reactiveOxygenElectronQuanta)))

    electrodeCollectedElectronQuanta electrodeBackReactionElectronQuanta : Nat
    extracellularPartition :
      extracellularElectronQuanta ≡
      electrodeCollectedElectronQuanta + electrodeBackReactionElectronQuanta

    hydrogenMoleculeQuanta : Nat
    -- A selected 2-electron product stoichiometry only. The full
    -- oxygen/water/proton reactions and chemical energetics are NOT proved.
    hydrogenElectronCount : fuelElectronQuanta ≡ 2 * hydrogenMoleculeQuanta

open PhotosystemWindow public

electrodeCollectionCannotExceedExtracellular :
  (w : PhotosystemWindow) ->
  Bound._≤_ (electrodeCollectedElectronQuanta w) (extracellularElectronQuanta w)
electrodeCollectionCannotExceedExtracellular w =
  Bound.transportUpper
    (Bound.sym (extracellularPartition w))
    (Bound.≤-append (electrodeCollectedElectronQuanta w)
                    (electrodeBackReactionElectronQuanta w))

sourceIndependentSyntheticFixture : PhotosystemWindow
sourceIndependentSyntheticFixture =
  photosystemWindow
    1200 200 1000 refl
    700 150 150 refl
    560 140 refl
    80 240 80
    80 80 refl
    55 25 refl
    40 refl

record QuantitativeBioGate : Set₁ where
  field
    ExperimentState : Set
    measuredPhotonInput : ExperimentState -> Nat
    inferredElectronTransfer : ExperimentState -> Nat
    electrodeCurrentSource : ExperimentState -> Nat
    electricalVoltageSource : ExperimentState -> Nat
    carbonProductSource : ExperimentState -> Nat
    fuelProductSource : ExperimentState -> Nat
    maintenanceEnergySource : ExperimentState -> Nat
    timeResolvedKineticAuthority : ExperimentState -> Nat

-- Explicitly no instance of QuantitativeBioGate is declared:
-- literature photocurrent at imposed potentiostat bias is not a
-- measured standalone solar-to-electric maximum-power point.
