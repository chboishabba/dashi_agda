module DASHI.Moonshine.Monster3BFiniteCharacterDeterminationLeanReceiptExact where

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT: EQUAL CHARACTERS DETERMINE SIMPLE FINITE REPS
--
-- Companion Lean branch `agent/e6-f3-exterior-square-maxcut-20261006`
-- source-writes
--
--   Integration.FiniteCharacterDeterminesSimpleRep.isoOfEqualCharacters
--
-- for finite-dimensional simple representations of a finite group over any
-- field in which the group order is invertible.
--
-- The proof route is exactly the one requested by the existing Agda interop:
--
--   FDRep.scalar_product_char_eq_finrank_equivariant
--   + equal characters
--   + nonzero identity in End(V)
--   -> positive cross equivariant-Hom finrank
--   -> nonzero equivariant morphism
--   -> CategoryTheory.isIso_of_hom_simple.
--
-- No algebraic-closure hypothesis is used.  This closes the GENERIC theorem
-- source surface, but not the Monster-specific transport: the concrete DASHI
-- finite-Heisenberg representation and actual H_zeta restriction must still be
-- packaged as compatible Lean FDReps and their DASHI class-character equality
-- must be transported to Mathlib character equality.
--
-- Lean is unavailable in the current execution environment, so theorem source
-- is written but exact-head kernel observation remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

leanRepository : String
leanRepository = "chboishabba/dashi_lean4"

leanBranch : String
leanBranch = "agent/e6-f3-exterior-square-maxcut-20261006"

leanOwnerPath : String
leanOwnerPath = "Integration/FiniteCharacterDeterminesSimpleRep.lean"

leanRegressionPath : String
leanRegressionPath = "Integration/FiniteCharacterDeterminesSimpleRepRegression.lean"

leanTheoremName : String
leanTheoremName = "Integration.FiniteCharacterDeterminesSimpleRep.isoOfEqualCharacters"

record Boundary : Set where
  constructor boundary
  field
    mathlibScalarProductHomFinrankLocated : Bool
    mathlibNonzeroSimpleMorphismIsIsoLocated : Bool
    leanEqualCharacterSimpleIsoSourceWritten : Bool
    algebraicClosureRequiredByLeanTheorem : Bool
    leanExactHeadKernelReceiptObserved : Bool
    monsterFiniteHeisenbergFDRepTransportPaid : Bool
    monsterActualHZetaFDRepTransportPaid : Bool
    dashiClassCharacterToMathlibCharacterTransportPaid : Bool
    fixedPhaseActualHZetaSameObjectPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true
  true
  true
  false
  false
  false
  false
  false
  false
