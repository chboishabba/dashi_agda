module DASHI.Moonshine.AbelE8RootTriadic243CountComparisonExact where

------------------------------------------------------------------------
-- EXACT SOURCE-PAID COUNT COMPARISON, NOT A LATTICE ISOMORPHISM
--
-- Root source: E8 indexed generated list of size 240.
-- Triadic source: actual T^5 / Kernel5 has 3^5=243 states,
-- and the punctured four-trit chart has 3^4-1=80.
--
--  240 = 3 * (3^4 - 1) = 3^5 - 3.
--
-- This is a numerical source-consistency check: there is NO selected
-- injection of the E8 root set into Kernel 5 here, no privileged three
-- missing states, no equality of E8 roots with ternary data, and no
-- theta/modular analyticity inferred from the matching cardinalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _∸_)

import DASHI.Algebra.Trit.E8RootEnumeration as Roots
import DASHI.Moonshine.JInvariant369RHAtomicTriadicCoefficientCrossPollinationExact as Triadic

e8ActualGeneratedRootCount : Nat
e8ActualGeneratedRootCount =
  Roots.indexedRootListLength Roots.combinedIndexedRoots

triadicFiveTritStateCount : Nat
triadicFiveTritStateCount = Triadic.fiveTritCount

triadicPuncturedFourTritStateCount : Nat
triadicPuncturedFourTritStateCount = Triadic.puncturedFourTritCount

originalE8GeneratedRootCountIs240 :
  e8ActualGeneratedRootCount ≡ 240
originalE8GeneratedRootCountIs240 =
  trans
    Roots.combinedIndexedRootsLengthIs240
    refl

originalFiveTritCountIs243 :
  triadicFiveTritStateCount ≡ 243
originalFiveTritCountIs243 =
  Triadic.fiveTritCountIs243

originalPuncturedFourTritCountIs80 :
  triadicPuncturedFourTritStateCount ≡ 80
originalPuncturedFourTritCountIs80 =
  Triadic.puncturedFourTritCountIs80

originalE8RootCountIsThreeTimesPuncturedFourTrit :
  e8ActualGeneratedRootCount ≡
    3 * triadicPuncturedFourTritStateCount
originalE8RootCountIsThreeTimesPuncturedFourTrit =
  trans
    originalE8GeneratedRootCountIs240
    (sym Triadic.twoFortyIsThreeTimesPuncturedFour)

originalE8RootCountPlusThreeIsFiveTritCount :
  e8ActualGeneratedRootCount + 3 ≡ triadicFiveTritStateCount
originalE8RootCountPlusThreeIsFiveTritCount
  rewrite originalE8GeneratedRootCountIs240
        | originalFiveTritCountIs243 = refl

originalFiveTritMinusThreeEqualsGeneratedE8Count :
  triadicFiveTritStateCount ∸ 3 ≡ e8ActualGeneratedRootCount
originalFiveTritMinusThreeEqualsGeneratedE8Count
  rewrite originalFiveTritCountIs243
        | originalE8GeneratedRootCountIs240 = refl

originalPuncturedFourTimesThreePlusThreeIsFiveTrit :
  3 * triadicPuncturedFourTritStateCount + 3 ≡
    triadicFiveTritStateCount
originalPuncturedFourTimesThreePlusThreeIsFiveTrit
  rewrite originalPuncturedFourTritCountIs80
        | originalFiveTritCountIs243 = refl
