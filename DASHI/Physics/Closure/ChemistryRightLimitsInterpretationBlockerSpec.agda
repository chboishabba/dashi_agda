module DASHI.Physics.Closure.ChemistryRightLimitsInterpretationBlockerSpec where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Explicit blocker spec for the next chemistry-facing step beyond the current
-- right-limits gate.
--
-- The intended next theorem would sharpen the physical interpretation of the
-- current right-limit observable while staying pre-spectral and
-- pre-scale-setting. At the moment two blockers remain:
--
-- 1. the interpretation contract is still missing:
--    there is no theorem-side MeasurementSurface/defect-channel law that says
--    what the current right-limit observable means as a chemistry-facing
--    quantity;
-- 2. the current atomic owner chain is cyclic:
--    AtomicChemistryRecoveryTheorem now depends downstream on the
--    AtomicPhotonuclearContact gate family, so importing the current theorem
--    chain as a single owner stack is not clean.
--
-- This module is intentionally standalone. It records the blocker precisely
-- without pretending the cyclic owner stack is already a clean theorem carrier.

record ChemistryRightLimitsInterpretationBlockerSpec : Setω where
  field
    blockerLabel : String
    blockedOwnerChain : List String
    requiredContracts : List String
    missingIngredients : List String
    nonClaimBoundary : List String

canonicalChemistryRightLimitsInterpretationBlockerSpec :
  ChemistryRightLimitsInterpretationBlockerSpec
canonicalChemistryRightLimitsInterpretationBlockerSpec =
  record
    { blockerLabel =
        "chemistry-right-limits-interpretation-and-cycle-blocker"
    ; blockedOwnerChain =
        "DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem"
        ∷ "DASHI.Physics.Closure.ClosedShellStabilityGateTheorem"
        ∷ "DASHI.Physics.Closure.ShellFillingDictionaryCompatibilityTheorem"
        ∷ "DASHI.Physics.Closure.ShellDictionaryRecoveryGateTheorem"
        ∷ "DASHI.Physics.Closure.AtomicPhotonuclearContactGateTheorem"
        ∷ "DASHI.Physics.Closure.ChemistryRightLimitsGateTheorem"
        ∷ []
    ; requiredContracts =
        "MeasurementSurface -> defect/Δ interpretation contract for the chemistry-facing lane"
        ∷ "metric/covariance propagation law for any chemistry-facing interpretation of the empirical surface"
        ∷ "a physically defended source-term law beyond empirical photonuclear packaging"
        ∷ "a chemistry-observable lift from quotient-visible shell class to a named pre-spectral chemistry-facing observable"
        ∷ []
    ; missingIngredients =
        "no clean theorem-side interpretation law explains what the current rightLimitGate means physically"
        ∷ "the current atom/chemistry owner stack is cyclic, so the next interpretation theorem cannot be landed cleanly on top of it without first breaking that owner cycle"
        ∷ "spectra and scale-setting remain explicitly deferred even after the interpretation blocker is removed"
        ∷ []
    ; nonClaimBoundary =
        "This blocker spec does not advance to spectra, scale-setting, ionization energies, bonding, periodic-table structure, nuclear dynamics, or finished chemistry"
        ∷ "It only records the next missing interpretation contract and the current cyclic owner-chain blocker"
        ∷ []
    }
