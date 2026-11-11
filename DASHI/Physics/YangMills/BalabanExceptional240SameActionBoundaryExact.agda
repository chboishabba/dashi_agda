module DASHI.Physics.YangMills.BalabanExceptional240SameActionBoundaryExact where

-- DASHI original cross-owner maximum-cut adapter.
-- Original physical symmetry owners: Wilson/Balaban lattice quadrature.
-- Exceptional root-count owner: MonsterThreeLocalE8LeechBridgeExact.
-- This is NOT a root-system identification and does NOT assert that
-- 240 hypercubic cells constitute an E8 root graph or Weyl orbit.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
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
  (RegularRoot Root Symmetry : Set)
  (cellAct : Symmetry → RegularRoot → RegularRoot)
  (rootAct : Symmetry → Root → Root) : Set₁ where
  field
    -- The *regular 240-cell subtype* must be supplied, not the full
    -- 256-element GridCell4 carrier with its 16 excluded infrared cells.
    forgetCell : RegularRoot → Grid.GridCell4
    toRoots : RegularRoot → Root
    fromRoots : Root → RegularRoot
    sourceAfterRoundTrip :
      (c : RegularRoot) → fromRoots (toRoots c) ≡ c
    targetAfterRoundTrip :
      (r : Root) → toRoots (fromRoots r) ≡ r
    intertwinesSelectedAction :
      (s : Symmetry) (c : RegularRoot) →
      toRoots (cellAct s c) ≡ rootAct s (toRoots c)
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

-- Existing physical owners already reduce this further:
-- BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact:
--    source reflection/permutation laws -> 7 generator certificates.
-- BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact:
--    literal recursive evaluator transports over 240 generated cells.
-- BalabanClayT4WilsonOneLoopHyperoctahedralGeneratorCertificateExact:
--    7 generators for full B4, 6 for fixed external axis.
-- Remaining leaf is a selected literal source theorem/certificate and
-- exact trig/interval environment compatibility, not geometric counting.
-- No physical certificate is forged here.

-- A genuine SAME-ACTION bijection necessarily transports each generator's
-- fixed-point locus; this is the first non-cardinality rejection test.
-- It does not depend on choosing the E8/root representation beforehand.

sourceFixedToRootFixed :
  ∀ {RegularRoot Root Symmetry : Set}
    {cellAct : Symmetry → RegularRoot → RegularRoot}
    {rootAct : Symmetry → Root → Root} →
  (comparison : SameAction240Comparison
    RegularRoot Root Symmetry cellAct rootAct) →
  (actor : Symmetry) (cell : RegularRoot) →
  cellAct actor cell ≡ cell →
  rootAct actor (SameAction240Comparison.toRoots comparison cell)
    ≡ SameAction240Comparison.toRoots comparison cell
sourceFixedToRootFixed comparison actor cell sourceFixed =
  trans
    (sym (SameAction240Comparison.intertwinesSelectedAction
      comparison actor cell))
    (cong (SameAction240Comparison.toRoots comparison) sourceFixed)

rootFixedToSourceFixed :
  ∀ {RegularRoot Root Symmetry : Set}
    {cellAct : Symmetry → RegularRoot → RegularRoot}
    {rootAct : Symmetry → Root → Root} →
  (comparison : SameAction240Comparison
    RegularRoot Root Symmetry cellAct rootAct) →
  (actor : Symmetry) (root : Root) →
  rootAct actor root ≡ root →
  cellAct actor (SameAction240Comparison.fromRoots comparison root)
    ≡ SameAction240Comparison.fromRoots comparison root
rootFixedToSourceFixed {cellAct = cellAct} {rootAct = rootAct}
  comparison actor root rootFixed =
  trans
    (sym (SameAction240Comparison.sourceAfterRoundTrip
      comparison (cellAct actor
        (SameAction240Comparison.fromRoots comparison root))))
    (trans
      (cong (SameAction240Comparison.fromRoots comparison)
        (SameAction240Comparison.intertwinesSelectedAction
          comparison actor
          (SameAction240Comparison.fromRoots comparison root)))
      (trans
        (cong (SameAction240Comparison.fromRoots comparison)
          (cong (rootAct actor)
            (SameAction240Comparison.targetAfterRoundTrip comparison root)))
        (cong (SameAction240Comparison.fromRoots comparison) rootFixed)))

-- Compare actual fixed-point *counts* on the regular-cell subtype and
-- selected exceptional root action. A mismatch refutes any inhabitant
-- of SameAction240Comparison for that same actor. Counting and selected
-- same-actor membership remain an external, finite computation task.
