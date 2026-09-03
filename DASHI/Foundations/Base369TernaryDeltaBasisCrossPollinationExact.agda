module DASHI.Foundations.Base369TernaryDeltaBasisCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact as Basis

------------------------------------------------------------------------
-- ONE RECURSIVE TERNARY FUNCTION BASIS, THREE STABLE SEMANTIC DEPTHS
--
-- The same T^n point-mass theorem applies at n=2,3,6 without identifying the
-- semantic roles of the resulting carriers:
--   T^2 : nonary/comparison/face-sheet level       (9)
--   T^3 : decision / Base369 voxel level           (27)
--   T^6 : situated appraisal / Heisenberg level    (729)
--
-- Shared recursive construction is a reusable algebraic identity; semantic
-- equality still requires a named bridge.
------------------------------------------------------------------------

NonaryCube9 : Set
NonaryCube9 = Basis.TritCube 2

DecisionCube27 : Set
DecisionCube27 = Basis.TritCube 3

AppraisalCube729 : Set
AppraisalCube729 = Basis.TritCube 6

nonaryDepth : Nat
nonaryDepth = 2

decisionDepth : Nat
decisionDepth = 3

appraisalDepth : Nat
appraisalDepth = 6

nonaryStateCount : Nat
nonaryStateCount = 9

decisionStateCount : Nat
decisionStateCount = 27

appraisalStateCount : Nat
appraisalStateCount = 729

nonaryCountIsThreeSquared : 3 * 3 ≡ nonaryStateCount
nonaryCountIsThreeSquared = refl

decisionCountIsThreeCubed : 3 * 3 * 3 ≡ decisionStateCount
decisionCountIsThreeCubed = refl

appraisalCountIsDecisionSquared : decisionStateCount * decisionStateCount ≡ appraisalStateCount
appraisalCountIsDecisionSquared = refl

------------------------------------------------------------------------
-- Exact point-mass decomposition at each named depth.
------------------------------------------------------------------------

nonaryFunctionDecomposition :
  (f : NonaryCube9 → C3.Cyclotomic3) →
  (x : NonaryCube9) →
  Basis.interpret (Basis.decompose f) x ≡ f x
nonaryFunctionDecomposition = Basis.decomposeExact

decisionFunctionDecomposition :
  (f : DecisionCube27 → C3.Cyclotomic3) →
  (x : DecisionCube27) →
  Basis.interpret (Basis.decompose f) x ≡ f x
decisionFunctionDecomposition = Basis.decomposeExact

appraisalFunctionDecomposition :
  (f : AppraisalCube729 → C3.Cyclotomic3) →
  (x : AppraisalCube729) →
  Basis.interpret (Basis.decompose f) x ≡ f x
appraisalFunctionDecomposition = Basis.decomposeExact

------------------------------------------------------------------------
-- The recursive depth relation itself is stable and useful:
-- appraisal T^6 = T^3 x T^3 at the carrier-shape level.  We do not identify
-- the two T^3 halves semantically here.
------------------------------------------------------------------------

data SharedTernaryBasisMeansSameSemanticCarrier : Set where
data SameCardinalityMeansSameCoordinateMeaning : Set where
data PointMassBasisCreatesMonsterAction : Set where

sharedBasisDoesNotCollapseSemanticCarriers :
  SharedTernaryBasisMeansSameSemanticCarrier → ⊥
sharedBasisDoesNotCollapseSemanticCarriers ()

sameCountDoesNotCreateMeaning : SameCardinalityMeansSameCoordinateMeaning → ⊥
sameCountDoesNotCreateMeaning ()

pointMassBasisDoesNotCreateMonsterAction : PointMassBasisCreatesMonsterAction → ⊥
pointMassBasisDoesNotCreateMonsterAction ()

record Base369TernaryDeltaBasisBoundary : Set where
  constructor base369-ternary-delta-basis-boundary
  field
    nonaryDepthUsesSameRecursiveBasis : Bool
    decisionDepthUsesSameRecursiveBasis : Bool
    appraisalDepthUsesSameRecursiveBasis : Bool
    appraisal729Is27Times27Cardinality : Bool
    semanticRolesCollapsedBySharedBasis : Bool
    MonsterActionCreatedByBasis : Bool

canonicalBase369TernaryDeltaBasisBoundary : Base369TernaryDeltaBasisBoundary
canonicalBase369TernaryDeltaBasisBoundary =
  base369-ternary-delta-basis-boundary
    true true true true false false
