module DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact where

------------------------------------------------------------------------
-- R445 ORIGINAL 1024 POSITIVE-BOND PROGRAM: SOURCE-FIRST CONSTRUCTOR.
--
-- Previously F16 had verified Python 41,792 adjacent swaps and a
-- source-written 128 selected-label duplicate decision; the physical
-- R445 Haar integration still lacked a *native Agda program*.
--
-- Here construct the ACTUAL native bond-label target list:
--   64 coarse original labels, each followed by its two native
--       selected original fine positive bonds, in their true order;
--   all original 1024 fine bonds that are NOT in those selected 128,
--       retaining original canonical enumeration order.
--
-- The original list membership uses F16's ORIGINAL bond DecEq and
-- the original native group/block origins (no new torus or field).
--
-- Reuse the new ORIGINAL R443 adjacent-sort program generator rather
-- than inventing another permutation algorithm. It produces a value
-- of Product.LinkPermutation 1024 for the physical R445 list.
--
-- Two closed finite Agda checks remain necessary: the literal list
-- length=1024 and the one original canonical-label vector equality.
-- These are exposed as explicit TYPES (not postulates or holes).
-- The Python swap count/hash cannot be promoted to kernel equality.
-- Both are supported by the independent original-bond enumerator;
-- exact-head compiler acceptance is still pending.
--
-- This source does not assert Haar existence, Wilson density equality
-- or any positive continuum Yang-Mills/OS mass-gap result.
-- Original Wilson/Balaban and DASHI source-owner attribution retained.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeSideFourPairDistinctCertificateExact as Pairs
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as C3
import DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact as Sort
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product

Bond : Set
Bond = C3.Bond

listLength : ∀ {A : Set} → List A → Nat
listLength [] = 0
listLength (_ ∷ rest) = 1 + listLength rest

-- The compiler-owned finite list -> Vec conversion, not an opaque
-- third-party bond enumeration or separate physical field.
listToVec :
  ∀ {A : Set} (items : List A) → Vec.Vec A (listLength items)
listToVec [] = Vec.[]
listToVec (item ∷ items) = Vec._∷_ item (listToVec items)

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (item ∷ rest) ys = item ∷ append rest ys

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  selectedOriginalFineBonds : List Bond
  selectedOriginalFineBonds =
    Pairs.selectedFinePairLabels
      (Native.sunExactSignedLinkGroup theory)
      Pairs.originalCoarseBondLabels

  -- The F16 predicate is a Boolean computation over the ORIGINAL
  -- exact decidable equality, with true precisely for non-members.
  remainingOriginalFineBonds : List Bond
  remainingOriginalFineBonds =
    go Pairs.originalFineBondLabels
    where
      go : List Bond → List Bond
      go [] = []
      go (bond ∷ tail) with Pairs.notMemberBoolean
        bond selectedOriginalFineBonds
      ... | true = bond ∷ go tail
      ... | false = go tail

  originalPairThenSpectatorLabels : List Bond
  originalPairThenSpectatorLabels =
    append selectedOriginalFineBonds remainingOriginalFineBonds

  -- Exactly ONE original native length check. The expected value is
  -- the true original positive-bond count, not a constant chosen by
  -- another finite model. The proof must be kernel-evaluated.
  originalPairSpectatorLengthGoal : Set
  originalPairSpectatorLengthGoal =
    listLength originalPairThenSpectatorLabels ≡ C3.Count

  originalPairSpectatorTargetVector :
    originalPairSpectatorLengthGoal → Vec.Vec Bond C3.Count
  originalPairSpectatorTargetVector lengthCheck =
    subst (Vec.Vec Bond) lengthCheck
      (listToVec originalPairThenSpectatorLabels)

  -- No externally chosen permutation program: the original R443
  -- native sorting generator computes it from the ORIGINAL labels.
  constructedOriginalPairSpectatorProgram :
    (lengthCheck : originalPairSpectatorLengthGoal) →
    Product.LinkPermutation C3.Count
  constructedOriginalPairSpectatorProgram lengthCheck =
    Sort.originalSortToTarget
      (originalPairSpectatorTargetVector lengthCheck)
      C3.canonicalLabelVector

  originalPairSpectatorCanonicalLabelGoal :
    (lengthCheck : originalPairSpectatorLengthGoal) → Set
  originalPairSpectatorCanonicalLabelGoal lengthCheck =
    Product.permuteLinks
      (constructedOriginalPairSpectatorProgram lengthCheck)
      C3.canonicalLabelVector
    ≡ originalPairSpectatorTargetVector lengthCheck

  -- These TWO closed equalities, plus original one-link Borel Haar,
  -- are the exact remaining *finite* geometric bridge to the F19
  -- weighted effective density on the literal 1024-link decoder.
  -- Do not collapse them to a Python receipt or a source-local refl.
