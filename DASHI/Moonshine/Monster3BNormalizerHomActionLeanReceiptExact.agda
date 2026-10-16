module DASHI.Moonshine.Monster3BNormalizerHomActionLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER SOURCE RECEIPT: NORMALIZER ACTION ON EQUIVARIANT HOM
--
-- Companion Lean #47 source-writes the canonical action
--
--   n.f = rho_W(n) o f o rho_H(n)^(-1)
--
-- on Hom_E(H,W).  Once actual normalizer lifts on H and W implement the same
-- conjugation action on E, this formula preserves E-equivariance.  Therefore
-- the multiplicity-space normalizer action is not independent third-carrier
-- data.
--
-- The actual Monster normalizer/projective lifts, their cocycle laws, absolute
-- zeta orientation and selected-phase 12+78 character transport remain open.
-- This source receipt imports no Lean theorem authority into Agda.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

repository : String
repository = "chboishabba/dashi_lean4"
branch : String
branch = "agent/e6-f3-exterior-square-maxcut-20261006"
sourcePath : String
sourcePath = "Synthesis/MonsterNormalizerHomAction.lean"

record Boundary : Set where
  constructor boundary
  field
    normalizerLiftInterfaceSourceWritten : Bool
    inducedHomNormalizerActionSourceWritten : Bool
    homPreservationFromConjugationSourceWritten : Bool
    independentMultiplicityActionStillRequired : Bool
    leanKernelAuthorityImportedIntoAgda : Bool
    actualMonsterNormalizerLiftsPaidByReceipt : Bool
    actualProjectiveCocycleLawsPaidByReceipt : Bool
    absoluteZetaOrientationPaidByReceipt : Bool
    actualTwelveSeventyEightCharacterTransportPaidByReceipt : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true false
  false false false false false
