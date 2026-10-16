module DASHI.Moonshine.Monster3BCharacterDeterminationLiveLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: LIVE TWO-SIMPLE CHARACTER DETERMINATION
--
-- Companion Lean #47 promotes the earlier DASHI character-multiplicity probe:
-- if an actual finite-group representation has character chi(T)+chi(S), with
-- T,S simple and nonisomorphic, character orthogonality gives Hom multiplicity
-- one for T and S and zero for every third simple type. Together with Maschke
-- this makes the abstract two-simple representation decomposition a compiler
-- consequence of a SAME-object character identity.
--
-- Thus a free-standing 12+78 action intertwiner is not the scientific input.
-- The remaining Monster data are the actual 6.Suz/normalizer multiplicity
-- representation, absolute selected-phase orientation, and transport of the
-- source-paid selected-phase 12+78 character onto that SAME action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

repository : String
repository = "chboishabba/dashi_lean4"
branch : String
branch = "agent/e6-f3-exterior-square-maxcut-20261006"
sourcePath : String
sourcePath = "Synthesis/MonsterCharacterDeterminationLive.lean"

record Boundary : Set where
  constructor boundary
  field
    equalSimpleCharacterClassifierSourceWritten : Bool
    twoSimpleCharacterMultiplicitySourceWritten : Bool
    otherSimpleMultiplicityZeroSourceWritten : Bool
    maschkeMakesCharacterMultiplicityRepresentationDetermining : Bool
    twelveSeventyEightIntertwinerStillIndependentInput : Bool
    leanKernelAuthorityImportedIntoAgda : Bool
    actualSuzukiMultiplicityActionPaidByReceipt : Bool
    absoluteZetaOrientationPaidByReceipt : Bool
    actualSuzukiMultiplicityCharacterTransportPaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true false
  false false false false
