module DASHI.Unified.GRQuantumUnificationProofTermBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)

import DASHI.Unified.GRQuantumUnification as Legacy
open import DASHI.Unified.GRQuantumProofTerms

------------------------------------------------------------------------
-- Hardened promotion seam for the merged Boolean-era facade.
--
-- `Legacy.TerminalUnificationWitness` remains available for compatibility, but
-- this module defines the promotion object that should be consumed by new code:
-- it requires both the legacy dependency-graph witness and the proposition-level
-- `TerminalGRQuantumProof`.

record HardenedTerminalUnificationWitness : Setω where
  constructor hardened-terminal-unification-witness
  field
    legacyWitness : Legacy.TerminalUnificationWitness
    proofTermWitness : TerminalGRQuantumProof
open HardenedTerminalUnificationWitness public

hardenedReading : HardenedTerminalUnificationWitness → Legacy.UnifiedReading
hardenedReading witness = Legacy.readingFromWitness (legacyWitness witness)

hardenedProofTerms :
  HardenedTerminalUnificationWitness → TerminalGRQuantumProof
hardenedProofTerms = proofTermWitness

legacyPromotionBoundaryText : String
legacyPromotionBoundaryText =
  "New consumers must use HardenedTerminalUnificationWitness.  Boolean equality receipts in the legacy facade are retained for compatibility but are not sufficient for proposition-level or physical promotion."
