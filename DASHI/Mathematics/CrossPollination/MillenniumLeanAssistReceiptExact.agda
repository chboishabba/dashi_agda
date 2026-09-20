module DASHI.Mathematics.CrossPollination.MillenniumLeanAssistReceiptExact where

------------------------------------------------------------------------
-- SIBLING LEAN PRODUCER CUSTODY FOR THE THREE-LANE MILLENNIUM CONTINUATION
--
-- This owner records source-level provenance only.
--
-- dashi_lean4 PR #10 carries two focused producers:
--
--   Synthesis/MillenniumHodgeCP1Quotient.lean
--     mathlib Projectivization quotient + lift/induction + CP1 chart overlap
--
--   Synthesis/MillenniumBSDRationalSquareBits.lean
--     rational sign-square invariance + padicValRat v2 parity-square invariance
--
-- The files are rooted in Synthesis.lean on the sibling branch.
--
-- IMPORTANT:
--   * GitHub Actions had not produced a Lean Action run at the observed head.
--   * No local Lean executable/build receipt was available in this environment.
--   * Therefore this receipt does NOT promote either producer to kernel-observed.
--   * Agda/Lean same-object transport is also separate and remains unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record MillenniumLeanAssistReceipt : Set where
  constructor millennium-lean-assist-receipt
  field
    repository :
      String

    branch :
      String

    pullRequest :
      String

    observedHead :
      String

    toolchain :
      String

    mathlibRevision :
      String

    hodgeSource :
      String

    bsdSource :
      String

    hodgeCP1QuotientSourcePresent :
      Bool

    hodgeMathlibProjectivizationReused :
      Bool

    bsdSquareBitsSourcePresent :
      Bool

    bsdMathlibPadicValRatReused :
      Bool

    sourcesRootedInSynthesis :
      Bool

    sourceEscapeAuditClean :
      Bool

    leanKernelReceiptObserved :
      Bool

    agdaSameObjectImportPaid :
      Bool

open MillenniumLeanAssistReceipt public

currentMillenniumLeanAssistReceipt :
  MillenniumLeanAssistReceipt
currentMillenniumLeanAssistReceipt =
  millennium-lean-assist-receipt
    "chboishabba/dashi_lean4"
    "agent/millennium-three-lane-lean-assist"
    "#10"
    "efca6d2e1d6ef5ae88c9b949d8e39d015a72311b"
    "leanprover/lean4:v4.28.0"
    "mathlib v4.28.0"
    "Synthesis/MillenniumHodgeCP1Quotient.lean"
    "Synthesis/MillenniumBSDRationalSquareBits.lean"
    true
    true
    true
    true
    true
    true
    false
    false
