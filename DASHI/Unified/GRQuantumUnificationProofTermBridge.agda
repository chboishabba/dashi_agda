module DASHI.Unified.GRQuantumUnificationProofTermBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)

import DASHI.Unified.GRQuantumUnification as Legacy
open import DASHI.Unified.GRQuantumStrictProofTerms

------------------------------------------------------------------------
-- Hardened promotion seam for the merged Boolean-era facade.
--
-- `Legacy.TerminalUnificationWitness` remains available for compatibility, but
-- new promotion requires the strict proposition-level object, including exact
-- Clifford/Spin refinements, typed common-substrate recovery, and the concrete
-- empirical-correspondence receipt.

record HardenedTerminalUnificationWitness : Setω where
  constructor hardened-terminal-unification-witness
  field
    legacyWitness : Legacy.TerminalUnificationWitness
    proofTermWitness : StrictTerminalGRQuantumProof
open HardenedTerminalUnificationWitness public

hardenedReading : HardenedTerminalUnificationWitness → Legacy.UnifiedReading
hardenedReading witness = Legacy.readingFromWitness (legacyWitness witness)

hardenedProofTerms :
  HardenedTerminalUnificationWitness → StrictTerminalGRQuantumProof
hardenedProofTerms = proofTermWitness

legacyPromotionBoundaryText : String
legacyPromotionBoundaryText =
  "New consumers must use HardenedTerminalUnificationWitness.  Boolean equality receipts in the legacy facade are retained for compatibility but are insufficient without StrictTerminalGRQuantumProof, shared-substrate recovery, and physical correspondence."
