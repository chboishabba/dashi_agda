module DASHI.Physics.Closure.NSTriadKNLuoThreeWayPairPartitionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Annales scientifiques de l'Ecole Normale Superieure 14 (1981).
-- DOI: 10.24033/asens.1404.
--
-- PURPOSE
-- Prove the finite combinatorial part of the Luo three-piece pair split.
-- A total classifier sends every mature pair to exactly one of
--
--   r_{p,1}, r_{p,2}, or u_{>p} tensor u_{>p}.
--
-- The recursively constructed sublists therefore reconstruct the complete
-- rational contribution fold exactly.  Transition and boundary policy is
-- encoded once in the classifier; no pair can be duplicated by construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)


data PairPiece : Set where
  rp1Piece : PairPiece
  rp2Piece : PairPiece
  hardTailPiece : PairPiece

record ThreeWayPartition (Pair : Set) : Set where
  constructor partition
  field
    rp1Pairs : List Pair
    rp2Pairs : List Pair
    hardTailPairs : List Pair

open ThreeWayPartition public

partitionPairs :
  ∀ {Pair : Set} →
  (Pair → PairPiece) →
  List Pair →
  ThreeWayPartition Pair
partitionPairs classify [] = partition [] [] []
partitionPairs classify (pair ∷ pairs)
  with classify pair | partitionPairs classify pairs
... | rp1Piece | partition rp1 rp2 tail =
  partition (pair ∷ rp1) rp2 tail
... | rp2Piece | partition rp1 rp2 tail =
  partition rp1 (pair ∷ rp2) tail
... | hardTailPiece | partition rp1 rp2 tail =
  partition rp1 rp2 (pair ∷ tail)

sumContributions :
  ∀ {Pair : Set} →
  (Pair → ℚ) →
  List Pair →
  ℚ
sumContributions contribution [] = 0ℚ
sumContributions contribution (pair ∷ pairs) =
  contribution pair + sumContributions contribution pairs

threeWayPartitionReconstructsFold :
  ∀ {Pair : Set}
    (classify : Pair → PairPiece)
    (contribution : Pair → ℚ)
    (pairs : List Pair) →
  sumContributions contribution pairs
  ≡ sumContributions contribution
      (rp1Pairs (partitionPairs classify pairs))
    + sumContributions contribution
        (rp2Pairs (partitionPairs classify pairs))
    + sumContributions contribution
        (hardTailPairs (partitionPairs classify pairs))
threeWayPartitionReconstructsFold classify contribution [] =
  solve []
threeWayPartitionReconstructsFold
  classify contribution (pair ∷ pairs)
  with classify pair | partitionPairs classify pairs
     | threeWayPartitionReconstructsFold classify contribution pairs
... | rp1Piece | partition rp1 rp2 tail | induction =
  rewrite induction =
  solve
    ( contribution pair
    ∷ sumContributions contribution rp1
    ∷ sumContributions contribution rp2
    ∷ sumContributions contribution tail
    ∷ []
    )
... | rp2Piece | partition rp1 rp2 tail | induction =
  rewrite induction =
  solve
    ( contribution pair
    ∷ sumContributions contribution rp1
    ∷ sumContributions contribution rp2
    ∷ sumContributions contribution tail
    ∷ []
    )
... | hardTailPiece | partition rp1 rp2 tail | induction =
  rewrite induction =
  solve
    ( contribution pair
    ∷ sumContributions contribution rp1
    ∷ sumContributions contribution rp2
    ∷ sumContributions contribution tail
    ∷ []
    )

record ClassifiedPair (Pair : Set) : Set where
  constructor classified
  field
    pair : Pair
    piece : PairPiece

open ClassifiedPair public

classifyPair :
  ∀ {Pair : Set} →
  (classify : Pair → PairPiece) →
  Pair →
  ClassifiedPair Pair
classifyPair classify pair = classified pair (classify pair)

eraseClassifiedPair :
  ∀ {Pair : Set} → ClassifiedPair Pair → Pair
eraseClassifiedPair (classified pair piece) = pair

eraseClassification :
  ∀ {Pair : Set}
    (classify : Pair → PairPiece)
    (pair : Pair) →
  eraseClassifiedPair (classifyPair classify pair) ≡ pair
eraseClassification classify pair = refl

threeWayPairPartitionClosed : Bool
threeWayPairPartitionClosed = true

threeWayPairFoldReconstructionClosed : Bool
threeWayPairFoldReconstructionClosed = true

threeWayPairPartitionClosedIsTrue :
  threeWayPairPartitionClosed ≡ true
threeWayPairPartitionClosedIsTrue = refl

threeWayPairFoldReconstructionClosedIsTrue :
  threeWayPairFoldReconstructionClosed ≡ true
threeWayPairFoldReconstructionClosedIsTrue = refl
