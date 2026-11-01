module DASHI.Unified.GRQuantumFiniteDiagnosticReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Governance receipt for the executable finite-model diagnostic.

scriptPath : String
scriptPath = "scripts/run_gr_quantum_finite_model_diagnostic.py"

outputPath : String
outputPath =
  "scripts/data/outputs/gr_quantum_finite_model_diagnostic.{json,md}"

record GRQuantumFiniteDiagnosticReceipt : Set where
  constructor finite-diagnostic-receipt
  field
    diagnosticScript : String
    diagnosticScriptIsCanonical : diagnosticScript ≡ scriptPath
    diagnosticOutput : String
    diagnosticOutputIsCanonical : diagnosticOutput ≡ outputPath
    finiteModelChecks : Bool
    finiteModelChecksAreEnabled : finiteModelChecks ≡ true
    continuumProofClaimed : Bool
    continuumProofClaimedIsFalse : continuumProofClaimed ≡ false
    physicalValidationClaimed : Bool
    physicalValidationClaimedIsFalse : physicalValidationClaimed ≡ false
    terminalUnificationClaimed : Bool
    terminalUnificationClaimedIsFalse : terminalUnificationClaimed ≡ false
    scope : String
open GRQuantumFiniteDiagnosticReceipt public

canonicalGRQuantumFiniteDiagnosticReceipt : GRQuantumFiniteDiagnosticReceipt
canonicalGRQuantumFiniteDiagnosticReceipt =
  finite-diagnostic-receipt
    scriptPath refl
    outputPath refl
    true refl
    false refl
    false refl
    false refl
    "reproducible finite/model checks only; no continuum, physical, or terminal authority"
