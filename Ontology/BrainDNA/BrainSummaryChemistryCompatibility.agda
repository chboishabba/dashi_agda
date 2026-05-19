module Ontology.BrainDNA.BrainSummaryChemistryCompatibility where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainSummaryPacketCompatibility as SummaryCompat using
  (BrainSummaryPacketCompatibilitySurface;
   brainSummaryPacketCompatibilitySurface;
   BrainSummaryPacketView; summaryStatePacketView)
open import Ontology.BrainDNA.BrainVocabularyPacketCompatibility using
  (stateToBridge)
open import Ontology.BrainDNA.PacketCodecBridge using (encodePacket)
open import Ontology.DNA.ChemistrySheetHamiltonian as Chemistry using
  (SheetCoordinates; sheetCoordinatesOf; sheetBandEnergy; crossBandEnergy;
   chemistryHamiltonianOf; countCrossBandCoupling;
   crossBandEnergy-sheetCoordinatesOf)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.Supervoxel4Adic using (Base)

------------------------------------------------------------------------
-- Narrow compatibility surface from the current brain summary / packet-view
-- boundary into the local DNA chemistry-sheet boundary.
--
-- This stays theorem-thin and honest on the current carrier:
-- the bridge only says that the summary-side packet view feeds a
-- line-major encoded packet whose chemistry-sheet coordinates and
-- derived local energies are exact at the existing packet boundary.

summarySheetCoordinates :
  ∀ {n} → BrainState n → SheetCoordinates n
summarySheetCoordinates st = sheetCoordinatesOf (encodePacket (stateToBridge st))

summarySheetBandEnergy :
  ∀ {n} → BrainState n → Nat
summarySheetBandEnergy st = sheetBandEnergy (summarySheetCoordinates st)

summaryCrossBandEnergy :
  ∀ {n} → BrainState n → Nat
summaryCrossBandEnergy st = crossBandEnergy (summarySheetCoordinates st)

summaryChemistryHamiltonian :
  ∀ {n} → BrainState n → Nat
summaryChemistryHamiltonian st =
  chemistryHamiltonianOf (encodePacket (stateToBridge st))

summaryChemistryWidthExact :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.width (summaryStatePacketView st) ≡ n
summaryChemistryWidthExact st = refl

summaryChemistryOrderLineMajor :
  ∀ {n} (st : BrainState n) →
  BrainSummaryPacketView.order (summaryStatePacketView st) ≡ lineMajor
summaryChemistryOrderLineMajor st = refl

summarySheetCoordinatesExact :
  ∀ {n} (st : BrainState n) →
  summarySheetCoordinates st
    ≡
  sheetCoordinatesOf (encodePacket (stateToBridge st))
summarySheetCoordinatesExact st = refl

summarySheetBandEnergyExact :
  ∀ {n} (st : BrainState n) →
  summarySheetBandEnergy st
    ≡
  sheetBandEnergy (sheetCoordinatesOf (encodePacket (stateToBridge st)))
summarySheetBandEnergyExact st = refl

summaryCrossBandEnergyStructured :
  ∀ {n} (st : BrainState n) →
  summaryCrossBandEnergy st
    ≡
  countCrossBandCoupling
    (SheetCoordinates.uSheet (summarySheetCoordinates st))
    (SheetCoordinates.vSheet (summarySheetCoordinates st))
summaryCrossBandEnergyStructured st =
  crossBandEnergy-sheetCoordinatesOf (encodePacket (stateToBridge st))

summaryChemistryHamiltonianExact :
  ∀ {n} (st : BrainState n) →
  summaryChemistryHamiltonian st
    ≡
  chemistryHamiltonianOf (encodePacket (stateToBridge st))
summaryChemistryHamiltonianExact st = refl

record BrainSummaryChemistryCompatibilitySurface : Set₂ where
  field
    summaryPacketSurface : BrainSummaryPacketCompatibilitySurface
    summaryOrder : ∀ {n} → BrainState n → ScanOrder
    summaryEncodedBases : ∀ {n} → BrainState n → Vec Base n
    summarySheet : ∀ {n} → BrainState n → SheetCoordinates n
    summarySheetEnergy : ∀ {n} → BrainState n → Nat
    summaryCrossEnergy : ∀ {n} → BrainState n → Nat
    summaryHamiltonian : ∀ {n} → BrainState n → Nat

brainSummaryChemistryCompatibilitySurface :
  BrainSummaryChemistryCompatibilitySurface
brainSummaryChemistryCompatibilitySurface = record
  { summaryPacketSurface = brainSummaryPacketCompatibilitySurface
  ; summaryOrder = λ st → lineMajor
  ; summaryEncodedBases = λ st → encodePacket (stateToBridge st)
  ; summarySheet = summarySheetCoordinates
  ; summarySheetEnergy = summarySheetBandEnergy
  ; summaryCrossEnergy = summaryCrossBandEnergy
  ; summaryHamiltonian = summaryChemistryHamiltonian
  }
