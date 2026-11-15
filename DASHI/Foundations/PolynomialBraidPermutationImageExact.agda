module DASHI.Foundations.PolynomialBraidPermutationImageExact where

------------------------------------------------------------------------
-- Braid group provenance: Artin three-strand presentation, B3 -> S3.
-- This module computes explicit WORD IMAGES under the existing S3 action.
-- It reuses the existing textile three-strand Yang--Baxter rewrite witness.
-- It is NOT an analytic coefficient-loop or π1 calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Foundations.PolynomialMonodromyTernaryQuaternionBridgeExact as M
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Combinatorics.TextileNFibreCalculusExact as Textile
import DASHI.Combinatorics.TextileBraidRewriteGroupoidExact as Rewrite
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic

BraidWordImage : Set
BraidWordImage = List M.BraidLoopGenerator

image : BraidWordImage → Perm.TriPermutation
image [] = Perm.permIdentity
image (g ∷ rest) = S3._∙_ (M.permutationImage g) (image rest)

singleGeneratorImage :
  (g : M.BraidLoopGenerator) →
  image (g ∷ []) ≡ M.permutationImage g
singleGeneratorImage M.swapAB = refl
singleGeneratorImage M.swapBC = refl
singleGeneratorImage M.undoSwapAB = refl
singleGeneratorImage M.undoSwapBC = refl

sigma0Sigma0 : BraidWordImage
sigma0Sigma0 = M.swapAB ∷ M.swapAB ∷ []

-- A nonempty positive two-crossing history becomes the identity permutation.
pureBraidPermutationImageIsIdentity :
  image sigma0Sigma0 ≡ Perm.permIdentity
pureBraidPermutationImageIsIdentity = refl

positiveHistoryNotLiterallyEmpty :
  sigma0Sigma0 ≡ [] → ⊥
positiveHistoryNotLiterallyEmpty ()

-- Three-strand Yang--Baxter: same S3 image and existing textile rewrite.
braidLeft : BraidWordImage
braidLeft = M.swapAB ∷ M.swapBC ∷ M.swapAB ∷ []

braidRight : BraidWordImage
braidRight = M.swapBC ∷ M.swapAB ∷ M.swapBC ∷ []

braidRelationRespectedByS3Image :
  image braidLeft ≡ image braidRight
braidRelationRespectedByS3Image = refl

textileActualYangBaxterRewrite :
  Rewrite.LocalBraidRewrite 3
    Textile.threeFibreYangBaxterLeft
    Textile.threeFibreYangBaxterRight
textileActualYangBaxterRewrite = Rewrite.threeFibreYangBaxterRewrite

inverseGeneratorSharesPermutationImage :
  image (M.swapAB ∷ []) ≡ image (M.undoSwapAB ∷ [])
inverseGeneratorSharesPermutationImage = refl

-- S3 commutators are exactly even. This is exhaustive over 6 x 6.
isEven : Perm.TriPermutation → Bool
isEven Perm.permIdentity = true
isEven Perm.permRotate = true
isEven Perm.permRotate2 = true
isEven Perm.permSwapLowMid = false
isEven Perm.permSwapLowHigh = false
isEven Perm.permSwapMidHigh = false

commutatorIsEven :
  (left right : Perm.TriPermutation) →
  isEven (M.permutationCommutator left right) ≡ true
commutatorIsEven Perm.permIdentity Perm.permIdentity = refl
commutatorIsEven Perm.permIdentity Perm.permRotate = refl
commutatorIsEven Perm.permIdentity Perm.permRotate2 = refl
commutatorIsEven Perm.permIdentity Perm.permSwapLowMid = refl
commutatorIsEven Perm.permIdentity Perm.permSwapLowHigh = refl
commutatorIsEven Perm.permIdentity Perm.permSwapMidHigh = refl
commutatorIsEven Perm.permRotate Perm.permIdentity = refl
commutatorIsEven Perm.permRotate Perm.permRotate = refl
commutatorIsEven Perm.permRotate Perm.permRotate2 = refl
commutatorIsEven Perm.permRotate Perm.permSwapLowMid = refl
commutatorIsEven Perm.permRotate Perm.permSwapLowHigh = refl
commutatorIsEven Perm.permRotate Perm.permSwapMidHigh = refl
commutatorIsEven Perm.permRotate2 Perm.permIdentity = refl
commutatorIsEven Perm.permRotate2 Perm.permRotate = refl
commutatorIsEven Perm.permRotate2 Perm.permRotate2 = refl
commutatorIsEven Perm.permRotate2 Perm.permSwapLowMid = refl
commutatorIsEven Perm.permRotate2 Perm.permSwapLowHigh = refl
commutatorIsEven Perm.permRotate2 Perm.permSwapMidHigh = refl
commutatorIsEven Perm.permSwapLowMid Perm.permIdentity = refl
commutatorIsEven Perm.permSwapLowMid Perm.permRotate = refl
commutatorIsEven Perm.permSwapLowMid Perm.permRotate2 = refl
commutatorIsEven Perm.permSwapLowMid Perm.permSwapLowMid = refl
commutatorIsEven Perm.permSwapLowMid Perm.permSwapLowHigh = refl
commutatorIsEven Perm.permSwapLowMid Perm.permSwapMidHigh = refl
commutatorIsEven Perm.permSwapLowHigh Perm.permIdentity = refl
commutatorIsEven Perm.permSwapLowHigh Perm.permRotate = refl
commutatorIsEven Perm.permSwapLowHigh Perm.permRotate2 = refl
commutatorIsEven Perm.permSwapLowHigh Perm.permSwapLowMid = refl
commutatorIsEven Perm.permSwapLowHigh Perm.permSwapLowHigh = refl
commutatorIsEven Perm.permSwapLowHigh Perm.permSwapMidHigh = refl
commutatorIsEven Perm.permSwapMidHigh Perm.permIdentity = refl
commutatorIsEven Perm.permSwapMidHigh Perm.permRotate = refl
commutatorIsEven Perm.permSwapMidHigh Perm.permRotate2 = refl
commutatorIsEven Perm.permSwapMidHigh Perm.permSwapLowMid = refl
commutatorIsEven Perm.permSwapMidHigh Perm.permSwapLowHigh = refl
commutatorIsEven Perm.permSwapMidHigh Perm.permSwapMidHigh = refl

c3ImageIsEven :
  (phase : Phase.Phase3) →
  isEven (Cyclic.embedC3InS3 phase) ≡ true
c3ImageIsEven Phase.phase0 = refl
c3ImageIsEven Phase.phase1 = refl
c3ImageIsEven Phase.phase2 = refl

commutatorOfTwoC3RotationsIsIdentity :
  (left right : Phase.Phase3) →
  M.permutationCommutator
    (Cyclic.embedC3InS3 left)
    (Cyclic.embedC3InS3 right)
  ≡ Perm.permIdentity
commutatorOfTwoC3RotationsIsIdentity Phase.phase0 Phase.phase0 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase0 Phase.phase1 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase0 Phase.phase2 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase1 Phase.phase0 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase1 Phase.phase1 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase1 Phase.phase2 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase2 Phase.phase0 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase2 Phase.phase1 = refl
commutatorOfTwoC3RotationsIsIdentity Phase.phase2 Phase.phase2 = refl

-- The S3 endpoint forgets a nontrivial positive history. This witness is
-- deliberately limited to syntactic words. Proving nontriviality in B3 needs
-- the braid exponent-sum invariant under the full presentation congruence.
data WordEndpointDeterminesHistory : Set where
wordEndpointDoesNotDetermineLiteralHistory :
  WordEndpointDeterminesHistory → ⊥
wordEndpointDoesNotDetermineLiteralHistory ()
