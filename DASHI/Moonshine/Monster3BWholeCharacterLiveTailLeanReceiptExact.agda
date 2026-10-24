module DASHI.Moonshine.Monster3BWholeCharacterLiveTailLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: LIVE WHOLE-CHARACTER TAIL
--
-- Companion Lean #47 now consolidates previously scattered generic producers:
--
-- * FDRep <-> group-algebra same-action/submodule adapter;
-- * whole-character simple-source classifier;
-- * Maschke semisimplicity under finite/nonmodular hypotheses;
-- * character-at-identity -> finrank ratio (including coefficient 90).
--
-- Hence an arbitrary Monster simple-type classifier, a separate semisimplicity
-- witness and separate 65610/729 ratio are not independent research inputs once
-- the SAME actual W_zeta|E and H_zeta are attached to this representation
-- theory and the actual-kernel ninety-copy character identity is transported to
-- those SAME carriers.
--
-- This receipt records Lean source status only. It imports no Lean theorem
-- authority into Agda and does not pay that final same-object character
-- transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

repository : String
repository = "chboishabba/dashi_lean4"
branch : String
branch = "agent/e6-f3-exterior-square-maxcut-20261006"

record Boundary : Set where
  constructor boundary
  field
    fdrepModuleAdapterSourceWritten : Bool
    wholeCharacterSimpleSourceClassifierSourceWritten : Bool
    maschkeSemisimplicitySourceWritten : Bool
    characterCoefficientDimensionRatioSourceWritten : Bool
    arbitrarySimpleTypeClassifierStillIndependentMonsterInput : Bool
    semisimplicityStillIndependentMonsterInput : Bool
    separateFinrankRatioStillIndependentMonsterInput : Bool
    leanKernelAuthorityImportedIntoAgda : Bool
    actualMonsterFDRepAttachmentPaidByReceipt : Bool
    actualMonsterWholeCharacterTransportPaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true
  false false false
  false false false
