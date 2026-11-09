{-# OPTIONS --safe #-}
module DASHI.Chemistry.IndustrialReactiveEnergyBalanceExact where

-- Source and ownership:
-- * Conservation/finite-path prior owner:
--   DASHI.Analysis.StoichiometricConservation (existing DASHI repository).
-- * Open reaction/exchange prior owner:
--   DASHI.Analysis.OpenSystemBalance and
--   DASHI.Biology.Cell.MetabolicOpenSystemBalance.
-- * Thermodynamic vocabulary:
--   DASHI.Physics.Laws.ThermodynamicStatisticalLaws.
-- * This adapter: DASHI/ChatGPT-assisted formalisation for the user, 2026-11-09.
-- * No attribution of these generic balances to Michael McLaren.
--
-- Exact finite bookkeeping only. No device efficacy, kinetic validity,
-- empirical calibration, patent ownership, or independent validation follows.
-- This module does NOT duplicate the existing conservation proof.
-- It transports the canonical source theorem to a selected industrial instance.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Analysis.StoichiometricConservation as SC

record IndustrialStoichiometricInstance
    (Reaction Vector Quantity State : Set) : Set₁ where
  field
    system : SC.StoichiometricSystem Reaction Vector Quantity State
    leftKernel : SC.LeftKernelConservation system

open IndustrialStoichiometricInstance public

industrialReactionPathCertificate :
  ∀ {Reaction Vector Quantity State}
  (I : IndustrialStoichiometricInstance Reaction Vector Quantity State) →
  SC.StoichiometricConservationCertificate (system I)
industrialReactionPathCertificate I =
  SC.certifyStoichiometricConservation (system I) (leftKernel I)

industrialReactionPathConserves :
  ∀ {Reaction Vector Quantity State}
  (I : IndustrialStoichiometricInstance Reaction Vector Quantity State) →
  (reactions : List Reaction) → (initial : State) →
  SC.quantity (system I)
    (SC.runReactionPath (system I) reactions initial)
    ≡ SC.quantity (system I) initial
industrialReactionPathConserves I =
  SC.reactionPathConserves (system I) (leftKernel I)

-- Every energy quantity in one record must be expressed in the same
-- energy unit and on the same heating-value convention.
-- Heat includes rejected/unrecovered energy; storage terms prevent
-- illicit use of transient battery or tank depletion as a cyclic gain.
record OpenEnergyStep : Set where
  field
    electricalInput : Nat
    chemicalInput : Nat
    storedBefore : Nat
    usefulOutput : Nat
    rejectedEnergy : Nat
    storedAfter : Nat

    firstLaw :
      (electricalInput + chemicalInput) + storedBefore
        ≡ (usefulOutput + rejectedEnergy) + storedAfter

open OpenEnergyStep public

energyLedgerIdentity :
  (s : OpenEnergyStep) →
  (electricalInput s + chemicalInput s) + storedBefore s
    ≡ (usefulOutput s + rejectedEnergy s) + storedAfter s
energyLedgerIdentity = firstLaw

-- A scoped negative control. A claim document can be present without a
-- calibrated measurement. Source metadata cannot turn one into the other.
data EvidenceClass : Set where
  patentDisclosure : EvidenceClass
  vendorAssertion : EvidenceClass
  instrumentMeasurement : EvidenceClass
  independentReplication : EvidenceClass

patentIsNotInstrumentMeasurement :
  patentDisclosure ≡ instrumentMeasurement → ⊥
patentIsNotInstrumentMeasurement ()

vendorAssertionIsNotIndependentReplication :
  vendorAssertion ≡ independentReplication → ⊥
vendorAssertionIsNotIndependentReplication ()

-- Device selection is disjoint; no palladium heater power is implicitly
-- charged to the low-voltage intake-electrolysis configuration.
data DeviceMode : Set where
  intakeElectrolysis : DeviceMode
  plasmaMembrane : DeviceMode
  carbonSynthesis : DeviceMode

intakeIsNotPlasma :
  intakeElectrolysis ≡ plasmaMembrane → ⊥
intakeIsNotPlasma ()

-- A device-specific ledger is required separately for each tested mode;
-- no numerical auxiliary load is asserted by this type.
record DeviceAuxiliaries : Set where
  field
    mode : DeviceMode
    electrolysisDraw : Nat
    plasmaDraw : Nat
    membraneHeaterDraw : Nat
    carbonCaptureDraw : Nat
    compressorDraw : Nat
    controlDraw : Nat

open DeviceAuxiliaries public

totalAuxiliaries : DeviceAuxiliaries → Nat
totalAuxiliaries s =
  electrolysisDraw s + plasmaDraw s + membraneHeaterDraw s
  + carbonCaptureDraw s + compressorDraw s + controlDraw s
