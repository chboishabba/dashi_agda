{-# OPTIONS --safe #-}
module DASHI.Chemistry.CarbonFuelRegenerationExact where

-- Prior art: Sabatier 1902 methanation reaction and conventional water
-- electrolysis/combustion chemistry; these are not McLaren inventions.
-- DASHI existing owner: DASHI.Analysis.StoichiometricConservation,
-- DASHI.Analysis.OpenSystemBalance and Chemistry.TransitionKernel.
-- This conditional carbon-inventory model: user-directed DASHI formalisation,
-- written with ChatGPT assistance (2026-11-09). No experimental or patent
-- validity is inferred from these proofs.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Chemistry.IndustrialReactiveEnergyBalanceExact as Ledger

-- In one capture/regeneration cycle, all departing carbon must be
-- allocated to recovered, emitted or stored carbon. Separate the portion
-- converted to next-cycle fuel from unconverted captured carbon.
record CarbonRecycleStep : Set where
  field
    exhaustCarbon : Nat
    recoveredCarbon : Nat
    emittedCarbon : Nat
    regeneratedCarbon : Nat
    unusedRecoveredCarbon : Nat
    captureBalance : exhaustCarbon ≡ recoveredCarbon + emittedCarbon
    synthesisBalance :
      recoveredCarbon ≡ regeneratedCarbon + unusedRecoveredCarbon

open CarbonRecycleStep public

carbonCaptureAccountsForEmissions :
  (s : CarbonRecycleStep) →
  exhaustCarbon s ≡ recoveredCarbon s + emittedCarbon s
carbonCaptureAccountsForEmissions = captureBalance

carbonSynthesisAccountsForResidual :
  (s : CarbonRecycleStep) →
  recoveredCarbon s ≡ regeneratedCarbon s + unusedRecoveredCarbon s
carbonSynthesisAccountsForResidual = synthesisBalance

-- Concrete non-ideal recovery regression. This is an illustration of
-- geometric attrition, not a measurement or material-specific law.
eightyPercentRound : CarbonRecycleStep
eightyPercentRound = record
  { exhaustCarbon = 100 ; recoveredCarbon = 80 ; emittedCarbon = 20
  ; regeneratedCarbon = 80 ; unusedRecoveredCarbon = 0
  ; captureBalance = refl ; synthesisBalance = refl }

eightyPercentNextRound : CarbonRecycleStep
eightyPercentNextRound = record
  { exhaustCarbon = 80 ; recoveredCarbon = 64 ; emittedCarbon = 16
  ; regeneratedCarbon = 64 ; unusedRecoveredCarbon = 0
  ; captureBalance = refl ; synthesisBalance = refl }

eightyPercentThirdRound : CarbonRecycleStep
eightyPercentThirdRound = record
  { exhaustCarbon = 64 ; recoveredCarbon = 51 ; emittedCarbon = 13
  ; regeneratedCarbon = 51 ; unusedRecoveredCarbon = 0
  ; captureBalance = refl ; synthesisBalance = refl }

twoRoundInventoryRegression :
  regeneratedCarbon eightyPercentNextRound ≡ 64
twoRoundInventoryRegression = refl

-- Explicit failure of an alleged no-input positive-work cycle.
-- The only assumptions are natural-number nonnegative energy values and
-- a closed, zero-input first-law equality 0 = useful + rejected.
noPositiveWorkUnderZeroInputs :
  (useful rejected : Nat) →
  0 ≡ useful + rejected → useful ≡ 0
noPositiveWorkUnderZeroInputs zero rejected equation = refl
noPositiveWorkUnderZeroInputs (suc useful) rejected ()

-- Two materially different physical configurations cannot share
-- one inferred device-identity witness without external evidence.
plasmaMembraneNotIntakeElectrolysis :
  Ledger.plasmaMembrane ≡ Ledger.intakeElectrolysis → ⊥
plasmaMembraneNotIntakeElectrolysis ()

-- Fuel-carbon regeneration is not hydrogen-energy regeneration:
-- atomic balance is not a certification of reaction yield or rate.
data ReactorEvidence : Set where
  selectedStoichiometry : ReactorEvidence
  measuredConversionYield : ReactorEvidence

stoichiometryIsNotMeasuredYield :
  selectedStoichiometry ≡ measuredConversionYield → ⊥
stoichiometryIsNotMeasuredYield ()
