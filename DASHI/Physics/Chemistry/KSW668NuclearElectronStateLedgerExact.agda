{-# OPTIONS --safe #-}
module DASHI.Physics.Chemistry.KSW668NuclearElectronStateLedgerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

------------------------------------------------------------------------
-- C1: REAL ORIGINAL NIST SPECTROSCOPY CHANNEL RECONCILIATION.
--
-- NIST ASD v5.12, DOI 10.18434/T4W30F:
-- N neutral -> N7+ summed ionization energies = 1486.0578277 eV.
-- C neutral -> C6+ summed ionization energies = 1030.10849879 eV.
-- H neutral -> H+ ionization energy = 13.598434599702 eV.
-- Values scaled to 10^-12 eV / unit are exact SOURCE-TRANSCRIBED
-- decimals, not uncertain nuclear precision or quantum electrodynamics.
--
-- Neutral-atom masses -> effective neutral C14 + neutral H Q value
-- is NOT the same nuclear final state as bare 14C6+ + p.
-- Actual single reaction from neutral 14N + n must conserve all
-- seven bound-or-free electrons. Recombination photons and final
-- ionization/acceleration must be separately observed.
------------------------------------------------------------------------

record ElectronChannel : Set where
  constructor electron-channel
  field
    reactantElectrons : Nat
    daughterCarbonElectrons : Nat
    hydrogenElectrons : Nat
    freeElectrons : Nat

open ElectronChannel public

neutralDaughters : ElectronChannel
neutralDaughters = electron-channel 7 6 1 0

ionAndFreeElectronDaughters : ElectronChannel
ionAndFreeElectronDaughters = electron-channel 7 6 0 1

bareNucleiWithFreeElectrons : ElectronChannel
bareNucleiWithFreeElectrons = electron-channel 7 0 0 7

electronInventoryMatches : ElectronChannel → Set
electronInventoryMatches c =
  reactantElectrons c
  ≡ daughterCarbonElectrons c
    + hydrogenElectrons c + freeElectrons c

neutralElectronReceipt : electronInventoryMatches neutralDaughters
neutralElectronReceipt = refl

ionPlusElectronReceipt :
  electronInventoryMatches ionAndFreeElectronDaughters
ionPlusElectronReceipt = refl

bareElectronReceipt :
  electronInventoryMatches bareNucleiWithFreeElectrons
bareElectronReceipt = refl

-- Decimal fixed-point binding values: 10^-12 eV per unit.
nitrogenElectronicBinding : Nat
nitrogenElectronicBinding = 1486057827700000

carbonElectronicBinding : Nat
carbonElectronicBinding = 1030108498790000

hydrogenElectronicBinding : Nat
hydrogenElectronicBinding = 13598434599702

nuclearMinusAtomicBindingCorrection : Nat
nuclearMinusAtomicBindingCorrection = 442350894310298

exactNISTIonizationBindingLedger :
  carbonElectronicBinding
  + hydrogenElectronicBinding
  + nuclearMinusAtomicBindingCorrection
  ≡ nitrogenElectronicBinding
exactNISTIonizationBindingLedger = refl

-- Source decimal nuclear Q benchmark in 10^-12 eV units:
-- Previous neutral masses: N14=14.00307400443 u, n=1.00866491595 u,
-- C14=14.0032419884 u, H=1.00782503223 u.
-- 2022 CODATA: 931.49410242 MeV/u, underlying isotope mass digits
-- and their uncertainties are NOT upgraded by decimal scaling.
atomicNeutralChannelQ : Nat
atomicNeutralChannelQ = 625870654542472395

bareNuclearChannelQ : Nat
bareNuclearChannelQ = 626313005436782693

neutralCarbonBareProtonFreeElectronChannelQ : Nat
neutralCarbonBareProtonFreeElectronChannelQ = 625857056107872693

bareCarbonBareProtonSevenElectronsChannelQ : Nat
bareCarbonBareProtonSevenElectronsChannelQ = 624826947609082693

originalBareNuclearQCorrection :
  atomicNeutralChannelQ + nuclearMinusAtomicBindingCorrection
  ≡ bareNuclearChannelQ
originalBareNuclearQCorrection = refl

originalNeutralCarbonProtonElectronQ :
  neutralCarbonBareProtonFreeElectronChannelQ
  + hydrogenElectronicBinding
  ≡ atomicNeutralChannelQ
originalNeutralCarbonProtonElectronQ = refl

originalBareCarbonSevenElectronsQ :
  bareCarbonBareProtonSevenElectronsChannelQ
  + nitrogenElectronicBinding
  ≡ bareNuclearChannelQ
originalBareCarbonSevenElectronsQ = refl

------------------------------------------------------------------------
-- This proves exact arithmetic on original tabulated electronic/atomic
-- inputs, and source-specific electron counting. It does NOT prove an
-- experimental nuclear differential cross section, a 3-body scattering
-- amplitude, or an instantaneous 2-body neutral-recombination event.
------------------------------------------------------------------------
