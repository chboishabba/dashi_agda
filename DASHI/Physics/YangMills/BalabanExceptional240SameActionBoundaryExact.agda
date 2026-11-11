module DASHI.Physics.YangMills.BalabanExceptional240SameActionBoundaryExact where

-- DASHI original cross-owner maximum-cut adapter.
-- Original physical symmetry owners: Wilson/Balaban lattice quadrature.
-- Exceptional root-count owner: MonsterThreeLocalE8LeechBridgeExact.
-- This is NOT a root-system identification and does NOT assert that
-- 240 hypercubic cells constitute an E8 root graph or Weyl orbit.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ)
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanClayT4HypercubicRepresentativeSumExact as Quad
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as E8

-- Independent source-object cardinalities, not source-object equivalence.
source240 :
  length Orbit.oneOuterCells + (length Orbit.twoOuterCells
    + (length Orbit.threeOuterCells + length Orbit.fourOuterCells))
    ≡ 240
source240 = Orbit.regularOrbitMultiplicitySum

exceptionalRoot240 : E8.e8RootCount ≡ 240
exceptionalRoot240 = E8.e8RootCountIs240

-- A four-orbit B4 decomposition and three *80-element* pieces cannot
-- match orbit-for-orbit. This is an exact obstruction ONLY to a bijection
-- that maps each entire source orbit bijectively onto a whole 80-block.
-- General linear intertwiners, refinements and subgroup restrictions
-- can mix or split pieces, so they are not ruled out.
twoOuterOrbitIsNotOneEightyBlock :
  length Orbit.twoOuterCells ≡ 80 → ⊥
twoOuterOrbitIsNotOneEightyBlock ()

fourOuterOrbitIsNotOneEightyBlock :
  length Orbit.fourOuterCells ≡ 80 → ⊥
fourOuterOrbitIsNotOneEightyBlock ()

-- Actual action / operator recognition must specify the *same actors*
-- and commute pointwise. Matching dimensions or coefficients is weaker.
record SameAction240Comparison
  (Root : Set)
  (Symmetry : Set)
  (cellAct : Symmetry → Grid.GridCell4 → Grid.GridCell4)
  (rootAct : Symmetry → Root → Root) : Set₁ where
  field
    regularSource : Grid.GridCell4 → Set
    targetIsRoot : Root → Set
    toRoots : Grid.GridCell4 → Root
    fromRoots : Root → Grid.GridCell4
    sourceAfterRoundTrip :
      (c : Grid.GridCell4) → fromRoots (toRoots c) ≡ c
    targetAfterRoundTrip :
      (r : Root) → toRoots (fromRoots r) ≡ r
    intertwinesSelectedAction :
      (s : Symmetry) (c : Grid.GridCell4) →
      toRoots (cellAct s c) ≡ rootAct s (toRoots c)
    respectsRegularSource : (c : Grid.GridCell4) →
      regularSource c → targetIsRoot (toRoots c)
    selectedRootInnerProductTransport : Set
    independentRootCarrierAuthentication : Set
    invarianceUnderSelectedExternalMomenta : Set

-- Reuse the pre-existing *physical* quadrature theorem, rather than
-- treating E8 count equality as proof of invariance of a physical integrand.
physicalInvariantSumReduction :
  ∀ {contribution : Grid.GridCell4 → ℚ} →
  Action.GeneratorInvariantRationalContribution contribution →
  Sums.sumRational Grid.regularGridCells contribution ≡
  Sums.sumRational Grid.regularGridCells
    (Quad.canonicalizedContribution contribution)
physicalInvariantSumReduction =
  Quad.regularSumCanonicalizes

-- P0 physical gate: instantiate GeneratorInvariantRationalContribution
-- for the literal selected Wilson/ghost/Haar scalar after respecting
-- fixed external momenta and interval enclosures. No instance here.
