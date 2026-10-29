module DASHI.Physics.Closure.R2P227729Orbit365RankSortPermutationExact where

------------------------------------------------------------------------
-- FINITE 729 ADDRESS PERMUTATION VIA SOURCE-OWNED DENSE PAIR RANK.
--
-- Ranked index owner:
--   R2P227729FourierObserverIncidenceExact.orderedPairRank
--   and its exact 0..728 dense pair729 enumeration.
-- Constructive sorting-permutation proof pattern:
--   NSTriadKNLiteralCriticalProductionRadialOrderExact
--   (insertByShellPermutation/sortByShellPermutation).
-- Finite sum transport:
--   R2P227729Orbit365PermutationReductionExact.
--
-- We sort the already-expanded 365 canonical C2-pair orbits by the
-- ORIGINAL ordered-pair rank, then use literal equality against the
-- original ordered 729-address list. No new quotient, no postulate,
-- no use of arithmetic equality as an unchecked permutation witness.
-- The final literal equality is an intentional, kernel-facing finite
-- normalization test. Kernel execution pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary using (yes; no)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP

import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729Orbit365PermutationReductionExact as OrbitPerm
import DASHI.Physics.Closure.R2P227729OrbitWeighted365ConvolutionExact as Orbit
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Full
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Herm
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

insertPairByRank :
  I.ModePair729 → List I.ModePair729 → List I.ModePair729
insertPairByRank pair [] = pair ∷ []
insertPairByRank pair (head ∷ tail)
  with I.orderedPairRank pair ≤? I.orderedPairRank head
... | yes _ = pair ∷ head ∷ tail
... | no _ = head ∷ insertPairByRank pair tail

sortPairsByRank : List I.ModePair729 → List I.ModePair729
sortPairsByRank [] = []
sortPairsByRank (pair ∷ rest) =
  insertPairByRank pair (sortPairsByRank rest)

insertPairByRankPermutation :
  (pair : I.ModePair729) (xs : List I.ModePair729) →
  insertPairByRank pair xs Perm.↭ (pair ∷ xs)
insertPairByRankPermutation pair [] = Perm.refl
insertPairByRankPermutation pair (head ∷ tail)
  with I.orderedPairRank pair ≤? I.orderedPairRank head
... | yes _ = Perm.refl
... | no _ =
  Perm.trans
    (Perm.prep head (insertPairByRankPermutation pair tail))
    (Perm.swap head pair Perm.refl)

sortPairsByRankPermutation :
  (xs : List I.ModePair729) → sortPairsByRank xs Perm.↭ xs
sortPairsByRankPermutation [] = Perm.refl
sortPairsByRankPermutation (pair ∷ rest) =
  Perm.trans
    (insertPairByRankPermutation pair (sortPairsByRank rest))
    (Perm.prep pair (sortPairsByRankPermutation rest))

-- The crucial closed kernel normal form: both sides contain the SAME
-- actual 729 pair records, in identical rank order, not only 729 counts.
-- Evaluating the insert-sort is the computational cost of this receipt.
rankSorted365ExpandedIsOriginal729 :
  sortPairsByRank OrbitPerm.expandedCanonicalPairs ≡ I.pair729
rankSorted365ExpandedIsOriginal729 = refl

sortedExpandedPermutationToOriginal :
  sortPairsByRank OrbitPerm.expandedCanonicalPairs Perm.↭ I.pair729
sortedExpandedPermutationToOriginal
  rewrite rankSorted365ExpandedIsOriginal729 = Perm.refl

actualOriginal729PermutesToExpanded365 :
  I.pair729 Perm.↭ OrbitPerm.expandedCanonicalPairs
actualOriginal729PermutesToExpanded365 =
  Perm.trans
    (PermP.↭-sym sortedExpandedPermutationToOriginal)
    (sortPairsByRankPermutation OrbitPerm.expandedCanonicalPairs)

-- No remaining CONDITIONAL permutation premise at the statement site.
-- Source-written full operator equality for arbitrary admissible real
-- Hermitian inputs and ALL 125 integer-frequency output modes.
orbit365FullHermitianConvolutionEquals729 :
  (a b : Herm.Hermitian27) (k : Full.WideCube125) →
  Orbit.unreducedConvolutionAt a b k
    ≡ Orbit.orbitWeightedConvolutionAt a b k
orbit365FullHermitianConvolutionEquals729 a b k =
  OrbitPerm.fullPairSumEqualsOrbitSumGivenPermutation
    a b k actualOriginal729PermutesToExpanded365

-- This is still the finite Q(omega) quadratic convolution, NOT the
-- physical vector-valued NS/Leray nonlinearity, C4/C5 DFT, or Clay.
