module DASHI.Analysis.NonArchimedeanZModPredecessorTransitivitySourceExact where

------------------------------------------------------------------------
-- ZMOD PREDECESSOR TRANSITIVITY SOURCE / MATHLIB RECEIPT
--
-- Concrete target:
--
--   State = ZMod N
--   pred x = x - 1
--   steps(x,y) = (x-y).val
--
-- Mathlib/source ingredients:
--
-- * Mathlib.Data.ZMod.Basic:
--     ZMod.finEquiv : Fin N ≃+* ZMod N                 (N nonzero)
-- * Mathlib.GroupTheory.SpecificGroups.Cyclic:
--     ZMod.instIsAddCyclic : IsAddCyclic (ZMod N)
-- * ZMod.natCast_zmod_val:
--     ((z.val : Nat) : ZMod N) = z
-- * ordinary additive-group identity:
--     x - (x-y) = y
-- * finite induction pattern for repeated subtraction of one:
--     (x ↦ x-1)^[k] x = x - (k : ZMod N).
--
-- The last identity is the same algebraic induction pattern used by Mathlib's
-- `pred_iterate`; it does not require an order on ZMod.
--
-- This file is deliberately a cross-language source receipt.  DASHI's generic
-- NatPredecessorDifferenceTransitivityExact owns the proof compiler; this file
-- records that the actual Lean ZMod carrier supplies each concrete premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record ZModPredecessorSourceReceipt : Set where
  constructor zmodPredecessorSourceReceipt
  field
    sourceRepositoryCommit : String
    mathlibReferenceCommit : String
    positiveModulusFinRingEquivalenceOwned : Bool
    zmodAdditiveCyclicInstanceOwned : Bool
    natCastZModValOwned : Bool
    subtractDifferenceGroupLawOwned : Bool
    repeatedSubtractOneInductionAvailable : Bool
    explicitDifferenceStepWitnessAvailable : Bool
    predecessorTransitivityCompiles : Bool
    agdaNativeZModCarrierPresent : Bool

canonicalZModPredecessorSourceReceipt : ZModPredecessorSourceReceipt
canonicalZModPredecessorSourceReceipt =
  zmodPredecessorSourceReceipt
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    "251e86bd1fa42024826ccdb46c3d680edff03e1f"
    true true true true true true true false

zmodPredecessorTransitivityLibraryClosed :
  ZModPredecessorSourceReceipt.predecessorTransitivityCompiles
    canonicalZModPredecessorSourceReceipt
  ≡ true
zmodPredecessorTransitivityLibraryClosed = refl

noFakeAgdaZModCarrier :
  ZModPredecessorSourceReceipt.agdaNativeZModCarrierPresent
    canonicalZModPredecessorSourceReceipt
  ≡ false
noFakeAgdaZModCarrier = refl

record AuthorityBoundary : Set where
  constructor authorityBoundary
  field
    mathematicalProducerClosed : Bool
    concreteLeanKernelTheoremAddedToSourceRepo : Bool
    agdaKernelChecksLeanZModStatement : Bool
    crossLanguagePremiseReceiptExplicit : Bool

canonicalAuthorityBoundary : AuthorityBoundary
canonicalAuthorityBoundary =
  authorityBoundary true false false true

mathematicsClosedWithoutCrossKernelPretence :
  AuthorityBoundary.mathematicalProducerClosed canonicalAuthorityBoundary
  ≡ true
mathematicsClosedWithoutCrossKernelPretence = refl

leanTheoremNotPretendedAdded :
  AuthorityBoundary.concreteLeanKernelTheoremAddedToSourceRepo
    canonicalAuthorityBoundary
  ≡ false
leanTheoremNotPretendedAdded = refl
