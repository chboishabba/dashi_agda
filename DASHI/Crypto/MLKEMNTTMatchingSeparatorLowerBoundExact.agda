module DASHI.Crypto.MLKEMNTTMatchingSeparatorLowerBoundExact where

------------------------------------------------------------------------
-- MATCHING-SEPARATOR LOWER BOUND FOR THE ROUND-17 NTT COUPLING GRAPH
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- The structural graph has two same-component cliques (constant / linear) and
-- one BaseCase cross-edge at each of 128 quadratic residue indices.  Any vertex
-- removal intended to eliminate *every* direct cross-component matching edge
-- must remove at least one endpoint from each of those 128 disjoint pairs.
--
-- This module proves that finite hitting-set lower bound exactly.  It does not
-- claim this is a treewidth theorem or a complete lower bound for all possible
-- conditional algorithms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-mono-≤)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.MLKEMNTTDataflowCouplingExact as NTT

boolCost : Bool → Nat
boolCost false = 0
boolCost true = 1

removedInPair : Bool × Bool → Nat
removedInPair (left , right) = boolCost left + boolCost right

removedTotal : List (Bool × Bool) → Nat
removedTotal [] = 0
removedTotal (pair ∷ rest) = removedInPair pair + removedTotal rest

length : {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

------------------------------------------------------------------------
-- Every matching edge is hit by at least one removed endpoint.
------------------------------------------------------------------------

data PairHit : Bool × Bool → Set where
  leftOnlyHit : PairHit (true , false)
  rightOnlyHit : PairHit (false , true)
  bothHit : PairHit (true , true)

pairHitCostsAtLeastOne :
  ∀ {pair} → PairHit pair → suc zero ≤ removedInPair pair
pairHitCostsAtLeastOne leftOnlyHit = s≤s z≤n
pairHitCostsAtLeastOne rightOnlyHit = s≤s z≤n
pairHitCostsAtLeastOne bothHit = s≤s z≤n

data AllPairsHit : List (Bool × Bool) → Set where
  none : AllPairsHit []
  more : ∀ {pair rest} → PairHit pair → AllPairsHit rest →
    AllPairsHit (pair ∷ rest)

matchingSeparatorNeedsOnePerEdge :
  ∀ {pairs} → AllPairsHit pairs → length pairs ≤ removedTotal pairs
matchingSeparatorNeedsOnePerEdge none = z≤n
matchingSeparatorNeedsOnePerEdge (more hit rest) =
  +-mono-≤
    (pairHitCostsAtLeastOne hit)
    (matchingSeparatorNeedsOnePerEdge rest)

------------------------------------------------------------------------
-- Exact 128-pair FIPS structural count.
------------------------------------------------------------------------

replicateLeftHit : Nat → List (Bool × Bool)
replicateLeftHit zero = []
replicateLeftHit (suc n) = (true , false) ∷ replicateLeftHit n

replicateAllHit : ∀ n → AllPairsHit (replicateLeftHit n)
replicateAllHit zero = none
replicateAllHit (suc n) = more leftOnlyHit (replicateAllHit n)

replicateLength : ∀ n → length (replicateLeftHit n) ≡ n
replicateLength zero = refl
replicateLength (suc n) =
  let open import Relation.Binary.PropositionalEquality using (cong)
  in cong suc (replicateLength n)

replicateRemovedTotal : ∀ n → removedTotal (replicateLeftHit n) ≡ n
replicateRemovedTotal zero = refl
replicateRemovedTotal (suc n) =
  let open import Relation.Binary.PropositionalEquality using (cong)
  in cong suc (replicateRemovedTotal n)

fipsMatchingEdgeCount : Nat
fipsMatchingEdgeCount = NTT.sourceCoefficientsPerScalarNTTCoordinate

fipsMatchingEdgeCountIs128 : fipsMatchingEdgeCount ≡ 128
fipsMatchingEdgeCountIs128 = refl

canonical128EdgeHittingMask : List (Bool × Bool)
canonical128EdgeHittingMask = replicateLeftHit fipsMatchingEdgeCount

canonical128MaskHitsEveryEdge : AllPairsHit canonical128EdgeHittingMask
canonical128MaskHitsEveryEdge = replicateAllHit fipsMatchingEdgeCount

canonicalSeparatorLowerBound :
  length canonical128EdgeHittingMask ≤ removedTotal canonical128EdgeHittingMask
canonicalSeparatorLowerBound =
  matchingSeparatorNeedsOnePerEdge canonical128MaskHitsEveryEdge

canonicalMaskRemovesExactly128 :
  removedTotal canonical128EdgeHittingMask ≡ 128
canonicalMaskRemovesExactly128 = replicateRemovedTotal 128

------------------------------------------------------------------------
-- Boundary: the structural matching itself has a 128-endpoint hitting floor.
-- A conditional algorithm may still exploit algebraic values, correlations or
-- non-separator methods.  No generic ML-KEM hardness conclusion follows.
------------------------------------------------------------------------

data MatchingSeparatorBoundary : Set where
  structuralMatchingNeeds128HitsOnly : MatchingSeparatorBoundary

matchingSeparatorBoundary : MatchingSeparatorBoundary
matchingSeparatorBoundary = structuralMatchingNeeds128HitsOnly
