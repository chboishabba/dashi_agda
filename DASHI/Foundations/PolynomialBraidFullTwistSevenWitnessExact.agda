module DASHI.Foundations.PolynomialBraidFullTwistSevenWitnessExact where

------------------------------------------------------------------------
-- THE FULL B3 BRAID RECORD IS STRICTLY RICHER THAN ITS S3 ROOT ENDPOINT.
--
-- Artin 1925 B3: σ0 σ1 σ0 = σ1 σ0 σ1. Birman 1974 and
-- Kassel--Turaev 2008: Δ²=(σ0 σ1)^3 is a CENTRAL full twist.
-- The positive full twist has braid exponent SUM 6, endpoint identity.
--
-- Instead of confusing braid history and permutation, construct the
-- concrete C7 QUOTIENT of exponent-sum. Both σ0 and σ1 act by +1;
-- their inverses act by -1. This respects the Artin braid relation
-- and two-sided cancellations. Hence the six-crossing full twist
-- is NONTRIVIAL in B3 although the S3 image is identity.
--
-- The group is the classical B3 -> Z -> Z/7 observer, not a claim
-- about SU2 spin or Alexander-Hatcher π1. q^3=-1 in SU2 is separate.
-- Uses #1414 exact braid-word S3 image; no duplicate braid owner.
-- Proof source-written / Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Foundations.PolynomialMonodromyTernaryQuaternionBridgeExact as M
import DASHI.Foundations.PolynomialBraidPermutationImageExact as Braid
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm

data Residue7 : Set where
  r0 r1 r2 r3 r4 r5 r6 : Residue7

next7 previous7 : Residue7 → Residue7
next7 r0 = r1
next7 r1 = r2
next7 r2 = r3
next7 r3 = r4
next7 r4 = r5
next7 r5 = r6
next7 r6 = r0
previous7 r0 = r6
previous7 r1 = r0
previous7 r2 = r1
previous7 r3 = r2
previous7 r4 = r3
previous7 r5 = r4
previous7 r6 = r5

nextPreviousCancel : (r : Residue7) →
  next7 (previous7 r) ≡ r
nextPreviousCancel r0 = refl
nextPreviousCancel r1 = refl
nextPreviousCancel r2 = refl
nextPreviousCancel r3 = refl
nextPreviousCancel r4 = refl
nextPreviousCancel r5 = refl
nextPreviousCancel r6 = refl

previousNextCancel : (r : Residue7) →
  previous7 (next7 r) ≡ r
previousNextCancel r0 = refl
previousNextCancel r1 = refl
previousNextCancel r2 = refl
previousNextCancel r3 = refl
previousNextCancel r4 = refl
previousNextCancel r5 = refl
previousNextCancel r6 = refl

-- The same signed exponent is assigned to BOTH braid generators.
stepBraidExponent : M.BraidLoopGenerator → Residue7 → Residue7
stepBraidExponent M.swapAB = next7
stepBraidExponent M.swapBC = next7
stepBraidExponent M.undoSwapAB = previous7
stepBraidExponent M.undoSwapBC = previous7

signedExponentMod7 : Braid.BraidWordImage → Residue7
signedExponentMod7 [] = r0
signedExponentMod7 (g ∷ gs) =
  stepBraidExponent g (signedExponentMod7 gs)

-- Braid relation holds AT EVERY input residue, not only at r0.
braidRelationPreservesExponent :
  (r : Residue7) →
  stepBraidExponent M.swapAB
    (stepBraidExponent M.swapBC
      (stepBraidExponent M.swapAB r))
  ≡
  stepBraidExponent M.swapBC
    (stepBraidExponent M.swapAB
      (stepBraidExponent M.swapBC r))
braidRelationPreservesExponent r = refl

-- Group word cancellation is respected by the C7 readout.
cancelAB :
  (r : Residue7) →
  stepBraidExponent M.swapAB
    (stepBraidExponent M.undoSwapAB r) ≡ r
cancelAB = nextPreviousCancel

cancelBC :
  (r : Residue7) →
  stepBraidExponent M.swapBC
    (stepBraidExponent M.undoSwapBC r) ≡ r
cancelBC = nextPreviousCancel

cancelInverseAB :
  (r : Residue7) →
  stepBraidExponent M.undoSwapAB
    (stepBraidExponent M.swapAB r) ≡ r
cancelInverseAB = previousNextCancel

cancelInverseBC :
  (r : Residue7) →
  stepBraidExponent M.undoSwapBC
    (stepBraidExponent M.swapBC r) ≡ r
cancelInverseBC = previousNextCancel

fullTwist : Braid.BraidWordImage
fullTwist =
  M.swapAB ∷ M.swapBC ∷
  M.swapAB ∷ M.swapBC ∷
  M.swapAB ∷ M.swapBC ∷ []

-- Six half-crossings vanish as a FINAL S3 permutation.
fullTwistHasIdentityS3Endpoint :
  Braid.image fullTwist ≡ Perm.permIdentity
fullTwistHasIdentityS3Endpoint = refl

-- But the full braid records a nonzero winding exponent.
fullTwistHasNonzeroSevenWinding :
  signedExponentMod7 fullTwist ≡ r6
fullTwistHasNonzeroSevenWinding = refl

sixIsNotZero : r6 ≡ r0 → ⊥
sixIsNotZero ()

nontrivialFullTwistInSignedExponentReadout :
  signedExponentMod7 fullTwist ≡ signedExponentMod7 [] → ⊥
nontrivialFullTwistInSignedExponentReadout ()

-- This is a genuine presentation-compatible obstruction because the
-- defining braid and inverse cancellation relations preserve the C7
-- observer. It is not the proof that fullTwist generates the centre:
-- centrality is an independently sourced Artin/Birman theorem.
