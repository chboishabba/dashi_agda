{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographyGravityUnruhTerminalExtensionExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkHolographyGravityTerminalCutsetExact as Terminal
import DASHI.Quantum.QuantumBirthmarkJacobsonUnruhNormalizationBoundaryExact as Unruh

------------------------------------------------------------------------
-- THIN TERMINAL EXTENSION
--
-- The main terminal cutset is shared with concurrent Jacobson work. This
-- extension records the later Unruh normalization max-cut without duplicating
-- that owner: scalar normalization is paid in sibling Lean, while the physical
-- Bisognano-Wichmann/wedge/KMS attachment remains live.
------------------------------------------------------------------------

record UnruhRefinedTerminalCut : Set where
  constructor unruhRefinedTerminalCut
  field
    priorTerminalCutsetRetained : Bool
    unruhScalarNormalizationOwned : Bool
    physicalBisognanoWichmannStillRequired : Bool
    physicalWedgeVacuumStateStillRequired : Bool
    accelerationProperTimeIdentificationStillRequired : Bool
    modularKMSAnalyticStripStillRequired : Bool
    scalarNormalizationDoesNotCloseJacobsonQFT : Bool
    scope : String

canonicalUnruhRefinedTerminalCut : UnruhRefinedTerminalCut
canonicalUnruhRefinedTerminalCut =
  unruhRefinedTerminalCut
    true
    true
    true
    true
    true
    true
    true
    "The terminal Jacobson cut is refined: the 2*pi boost-KMS/proper-time scalar normalization is paid, but the physical Bisognano-Wichmann wedge theorem, vacuum/state identification, KMS analytic strip and acceleration-to-proper-time attachment remain live."

unruhScalarNormalizationOwned : Bool
unruhScalarNormalizationOwned = Unruh.boostKMSNormalizationSourceWritten

physicalBisognanoWichmannStillRequired : Bool
physicalBisognanoWichmannStillRequired =
  Unruh.physicalBisognanoWichmannStillRequired

accelerationProperTimeIdentificationStillRequired : Bool
accelerationProperTimeIdentificationStillRequired =
  Unruh.accelerationProperTimeIdentificationStillRequired

modularKMSAnalyticStripStillRequired : Bool
modularKMSAnalyticStripStillRequired =
  Unruh.modularKMSAnalyticStripStillRequired

priorTerminalPhysicalCutsetStillAvailable : Terminal.TerminalPhysicalCutset
priorTerminalPhysicalCutsetStillAvailable = Terminal.canonicalTerminalPhysicalCutset
