module DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Degeneracy maps / oldforms and prime-to-added-level Hecke action.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- The permutation representation of S3 decomposes as 1 + std.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full level-2 change-of-frame action.
--
-- DASHI CONTRIBUTION
--
-- Strengthen P11MarkedLevel44OldspaceWeldExact.  The previous file correctly
-- identified the three-dimensional isotypic space
--
--   Brandt-newform + deck-standard
--
-- with the dimension pattern of the d=1,2,4 level-44 old copies, but its named
-- basis (Brandt,std1,std2) is an ISOTYPIC basis, not the literal permutation
-- basis of the three degeneracy copies.
--
-- Here we construct the actual integral permutation basis inside the SAME
-- marked five-state carrier:
--
--   v1 = (-3,-3,6,0,0)
--   v2 = (-3,-3,0,6,0)
--   v4 = (-3,-3,0,0,6).
--
-- The genuine marked deck generators act by
--
--   r : v1 -> v2 -> v4 -> v1
--   s : v1 -> v1, v2 <-> v4,
--
-- exactly the S3 permutation action on the old-copy labels {1,2,4}.
-- Moreover each vi has the SAME source-native Hecke eigenvalues at the three
-- currently constructed good primes:
--
--   T3=-1, T5=+1, T7=-2.
--
-- Thus the marked arithmetic now realizes the complete finite oldform-copy
-- pattern as an honest deck-permutation basis, not merely as three labels.
--
-- IMPORTANT BOUNDARY
-- This still does not identify vi with the analytic degeneracy forms
-- f(z),f(2z),f(4z).  The remaining same-object theorem is precisely a
-- deck- and Hecke-equivariant map between these two permutation modules.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Moonshine.P11MarkedLevel44OldspaceWeldExact as Old
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7

------------------------------------------------------------------------
-- Literal deck action on coefficient vectors.
--
-- deckR on states fixes a0,a1 and cycles b0->b1->b2->b0.  Therefore on
-- basis coefficients it sends (b0,b1,b2) to (b2,b0,b1).
-- deckS swaps a0/a1, fixes b0 and swaps b1/b2.
------------------------------------------------------------------------

deckR5 : S3.Int5 → S3.Int5
deckR5 v = S3.int5
  (S3.a0c v) (S3.a1c v)
  (S3.b2c v) (S3.b0c v) (S3.b1c v)

deckS5 : S3.Int5 → S3.Int5
deckS5 v = S3.int5
  (S3.a1c v) (S3.a0c v)
  (S3.b0c v) (S3.b2c v) (S3.b1c v)

------------------------------------------------------------------------
-- The true old-copy permutation basis inside the marked module.
------------------------------------------------------------------------

oldCopyVector : Old.OldCopy44 → S3.Int5
oldCopyVector Old.copy1 =
  S3.int5 (-[1+ 2 ]) (-[1+ 2 ]) (+ 6) (+ 0) (+ 0)
oldCopyVector Old.copy2 =
  S3.int5 (-[1+ 2 ]) (-[1+ 2 ]) (+ 0) (+ 6) (+ 0)
oldCopyVector Old.copy4 =
  S3.int5 (-[1+ 2 ]) (-[1+ 2 ]) (+ 0) (+ 0) (+ 6)

oldCopyDeckRIntertwines :
  (copy : Old.OldCopy44) →
  deckR5 (oldCopyVector copy) ≡ oldCopyVector (Old.oldDeckR copy)
oldCopyDeckRIntertwines Old.copy1 = refl
oldCopyDeckRIntertwines Old.copy2 = refl
oldCopyDeckRIntertwines Old.copy4 = refl

oldCopyDeckSIntertwines :
  (copy : Old.OldCopy44) →
  deckS5 (oldCopyVector copy) ≡ oldCopyVector (Old.oldDeckS copy)
oldCopyDeckSIntertwines Old.copy1 = refl
oldCopyDeckSIntertwines Old.copy2 = refl
oldCopyDeckSIntertwines Old.copy4 = refl

------------------------------------------------------------------------
-- Relation with the previous isotypic basis.
--
-- v1 = Brandt + 2 std1 + 2 std2
-- v2 = Brandt - 4 std1 + 2 std2
-- v4 = Brandt + 2 std1 - 4 std2.
--
-- These exact equalities prove that the permutation basis spans the same
-- rational three-space as Brandt + standard; no new arithmetic carrier has
-- been introduced.
------------------------------------------------------------------------

v1IsIsotypicCombination :
  oldCopyVector Old.copy1
  ≡ S3.add5 S3.brandtNewformVector
      (S3.add5
        (S3.scale5 (+ 2) S3.standardVector1)
        (S3.scale5 (+ 2) S3.standardVector2))
v1IsIsotypicCombination = refl

v2IsIsotypicCombination :
  oldCopyVector Old.copy2
  ≡ S3.add5 S3.brandtNewformVector
      (S3.add5
        (S3.scale5 (-[1+ 3 ]) S3.standardVector1)
        (S3.scale5 (+ 2) S3.standardVector2))
v2IsIsotypicCombination = refl

v4IsIsotypicCombination :
  oldCopyVector Old.copy4
  ≡ S3.add5 S3.brandtNewformVector
      (S3.add5
        (S3.scale5 (+ 2) S3.standardVector1)
        (S3.scale5 (-[1+ 3 ]) S3.standardVector2))
v4IsIsotypicCombination = refl

-- Their sum is three times the deck-trivial Brandt-newform vector.
oldCopyOrbitSumIsThreeBrandt :
  S3.add5 (oldCopyVector Old.copy1)
    (S3.add5 (oldCopyVector Old.copy2) (oldCopyVector Old.copy4))
  ≡ S3.scale5 (+ 3) S3.brandtNewformVector
oldCopyOrbitSumIsThreeBrandt = refl

------------------------------------------------------------------------
-- Genuine marked Hecke action on every permutation basis vector.
------------------------------------------------------------------------

oldCopyT3Eigen :
  (copy : Old.OldCopy44) →
  S3.markedT3Action (oldCopyVector copy)
  ≡ S3.scale5 (-[1+ 0 ]) (oldCopyVector copy)
oldCopyT3Eigen Old.copy1 = refl
oldCopyT3Eigen Old.copy2 = refl
oldCopyT3Eigen Old.copy4 = refl

oldCopyT5Eigen :
  (copy : Old.OldCopy44) →
  S3.markedT5Action (oldCopyVector copy)
  ≡ S3.scale5 (+ 1) (oldCopyVector copy)
oldCopyT5Eigen Old.copy1 = refl
oldCopyT5Eigen Old.copy2 = refl
oldCopyT5Eigen Old.copy4 = refl

oldCopyT7Eigen :
  (copy : Old.OldCopy44) →
  T7.markedT7Action (oldCopyVector copy)
  ≡ S3.scale5 (-[1+ 1 ]) (oldCopyVector copy)
oldCopyT7Eigen Old.copy1 = refl
oldCopyT7Eigen Old.copy2 = refl
oldCopyT7Eigen Old.copy4 = refl

------------------------------------------------------------------------
-- The deck-permutation basis therefore carries a single common Hecke
-- character at all source-native good primes while retaining nontrivial deck
-- motion.  This is exactly the finite oldspace pattern.
------------------------------------------------------------------------

record P11MarkedLevel44PermutationOldspaceBoundary : Set where
  field
    integralPermutationBasisConstructed : Bool
    deckRPermutesCopiesExactly : Bool
    deckSPermutesCopiesExactly : Bool
    permutationBasisInsideBrandtPlusStandard : Bool
    t3CommonEigencharacter : Bool
    t5CommonEigencharacter : Bool
    t7CommonEigencharacter : Bool
    analyticDegeneracySameObjectMapConstructed : Bool

canonicalP11MarkedLevel44PermutationOldspaceBoundary :
  P11MarkedLevel44PermutationOldspaceBoundary
canonicalP11MarkedLevel44PermutationOldspaceBoundary = record
  { integralPermutationBasisConstructed = true
  ; deckRPermutesCopiesExactly = true
  ; deckSPermutesCopiesExactly = true
  ; permutationBasisInsideBrandtPlusStandard = true
  ; t3CommonEigencharacter = true
  ; t5CommonEigencharacter = true
  ; t7CommonEigencharacter = true
  ; analyticDegeneracySameObjectMapConstructed = false
  }
