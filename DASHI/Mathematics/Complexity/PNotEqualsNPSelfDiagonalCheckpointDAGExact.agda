module DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalCheckpointDAGExact where

------------------------------------------------------------------------
-- SELF-DIAGONAL CHECKPOINT CERTIFICATES: NAIVE RECURSION NO-GO
--
-- Proposed idea:
--
--   C_0 -> C_(T/2) -> C_T
--
-- recursively certifying the two half-runs.
--
-- This file proves the elementary but important accounting fact: recursive
-- bisection ALONE does not compress a trajectory.  At depth d, the canonical
-- binary decomposition has exactly 2^d leaf transition obligations.
--
-- Therefore any sub-T certificate must obtain genuine DAG sharing or a
-- stronger transition certificate; writing the same recursion as a tree is
-- not a succinctness theorem.
--
-- This is repo-native mathematics.  No external source is attributed this
-- counting lemma.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

------------------------------------------------------------------------
-- Binary power and canonical recursive checkpoint tree.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc depth) =
  pow2 depth + pow2 depth

data CheckpointTree : Nat → Set where
  transitionLeaf :
    CheckpointTree zero

  splitCheckpoint :
    ∀ {depth} →
    CheckpointTree depth →
    CheckpointTree depth →
    CheckpointTree (suc depth)

canonicalRecursiveSplit :
  (depth : Nat) →
  CheckpointTree depth
canonicalRecursiveSplit zero =
  transitionLeaf
canonicalRecursiveSplit (suc depth) =
  splitCheckpoint
    (canonicalRecursiveSplit depth)
    (canonicalRecursiveSplit depth)

leafObligations :
  ∀ {depth} →
  CheckpointTree depth →
  Nat
leafObligations transitionLeaf =
  suc zero
leafObligations (splitCheckpoint left right) =
  leafObligations left + leafObligations right

canonicalRecursiveSplitLeafCount :
  (depth : Nat) →
  leafObligations (canonicalRecursiveSplit depth)
  ≡ pow2 depth
canonicalRecursiveSplitLeafCount zero =
  refl
canonicalRecursiveSplitLeafCount (suc depth)
    rewrite canonicalRecursiveSplitLeafCount depth =
  refl

------------------------------------------------------------------------
-- If a T-step trajectory has T = 2^d primitive transition obligations, the
-- naive recursive split still has T leaves.
------------------------------------------------------------------------

naiveCheckpointRecursionDoesNotCompressPowerOfTwoRun :
  (depth runtime : Nat) →
  runtime ≡ pow2 depth →
  leafObligations (canonicalRecursiveSplit depth)
  ≡ runtime
naiveCheckpointRecursionDoesNotCompressPowerOfTwoRun
    depth .(pow2 depth) refl =
  canonicalRecursiveSplitLeafCount depth

------------------------------------------------------------------------
-- Internal-node accounting.
------------------------------------------------------------------------

treeNodes :
  ∀ {depth} →
  CheckpointTree depth →
  Nat
treeNodes transitionLeaf =
  suc zero
treeNodes (splitCheckpoint left right) =
  suc (treeNodes left + treeNodes right)

canonicalTreeNodes :
  (depth : Nat) →
  treeNodes (canonicalRecursiveSplit (suc depth))
  ≡ suc
      (treeNodes (canonicalRecursiveSplit depth)
       + treeNodes (canonicalRecursiveSplit depth))
canonicalTreeNodes depth =
  refl

------------------------------------------------------------------------
-- Sharing boundary.
--
-- A DAG implementation may be smaller only when it proves that multiple tree
-- obligations can reuse one certified subclaim.  The syntax below deliberately
-- does NOT assert such identifications.  A future theorem has to construct
-- them from the special self-generated computation, rather than from recursive
-- bisection alone.
------------------------------------------------------------------------

record SharedCheckpointCertificate (depth : Nat) : Set₁ where
  field
    sharedNodeCount : Nat

    -- The sharing implementation must separately justify coverage of the
    -- primitive transition obligations.  No generic "DAG is smaller" axiom is
    -- supplied here.
    coversCanonicalSplit :
      Set

open SharedCheckpointCertificate public
