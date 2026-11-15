module DASHI.Reasoning.TrialecticCarryDepthExpansionPolicyExact where

------------------------------------------------------------------------
-- NEXT-DEPTH EXPANSION POLICY FOR TRIALECTIC CELL CARRY
--
-- TrialecticThreeCellCarryDepthExact deliberately emits one mediated T^3 cell
-- while retaining the whole previous structured state.  A next structured
-- trialectic state, however, contains a compatible T^18 boundary plus an
-- irreducible face.  This file makes the missing expansion data explicit.
--
-- An expansion policy embeds the carried T^3 seed as participant A of a new
-- structured state and supplies all remaining boundary cells and the face.
-- Such a policy is easy to construct, but is not forced by the seed:
--
--   * the same seed admits distinct compatible boundaries (different B);
--   * even with the same boundary, the face may differ.
--
-- Hence a one-cell carry is not an automatic all-depth dynamics.  Iteration
-- requires an explicit expansion policy at each step plus coherence between
-- those choices.  This is underdetermination, not impossibility.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Core.Prelude using (⊥; cong)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticThreeCellCarryDepthExact as CarryDepth
import DASHI.Reasoning.TrialecticC3GlobalNaturalityNoGoExact as C3NoGo

record NextStructuredExpansionPolicy : Set₁ where
  constructor next-structured-expansion-policy
  field
    expand :
      Cell.TrialecticBasis3Cell →
      Cell.StructuredTrialecticState

    carriedSeedEmbeddedAtA :
      (seed : Cell.TrialecticBasis3Cell) →
      Cell.leftCell
        (Cell.edgeAB
          (Cell.structuredBoundary (expand seed)))
      ≡ seed

open NextStructuredExpansionPolicy public

expandWith :
  Cell.TrialecticBasis3Cell →
  Face.TriadicFaceRelation →
  Cell.TrialecticBasis3Cell →
  Cell.StructuredTrialecticState
expandWith fixedB face seed =
  Cell.structured-trialectic-state
    (Cell.coordinatesToCompatibleBoundary
      (Cell.structured-boundary-coordinates
        seed
        fixedB
        Fabric.origin
        Fabric.origin
        Fabric.origin
        Fabric.origin))
    face

policyWith :
  Cell.TrialecticBasis3Cell →
  Face.TriadicFaceRelation →
  NextStructuredExpansionPolicy
policyWith fixedB face =
  next-structured-expansion-policy
    (expandWith fixedB face)
    (λ seed → refl)

originReciprocalPolicy : NextStructuredExpansionPolicy
originReciprocalPolicy =
  policyWith Fabric.origin Face.reciprocalFace

positiveBReciprocalPolicy : NextStructuredExpansionPolicy
positiveBReciprocalPolicy =
  policyWith Fabric.positiveCorner Face.reciprocalFace

originUnderdeterminedPolicy : NextStructuredExpansionPolicy
originUnderdeterminedPolicy =
  policyWith Fabric.origin Face.underdeterminedFace

selectedSeed : Cell.TrialecticBasis3Cell
selectedSeed = Fabric.negativeCorner

boundaryParticipantB :
  Cell.CompatibleThreeCellTrialecticBoundary →
  Cell.TrialecticBasis3Cell
boundaryParticipantB boundary =
  Cell.rightCell (Cell.edgeAB boundary)

sameSeedDifferentBoundary :
  Cell.structuredBoundary (expand originReciprocalPolicy selectedSeed)
  ≡
  Cell.structuredBoundary (expand positiveBReciprocalPolicy selectedSeed)
  →
  ⊥
sameSeedDifferentBoundary equality =
  C3NoGo.originNotPositiveCorner
    (cong boundaryParticipantB equality)

sameBoundaryAcrossFacePolicies :
  Cell.structuredBoundary (expand originReciprocalPolicy selectedSeed)
  ≡
  Cell.structuredBoundary (expand originUnderdeterminedPolicy selectedSeed)
sameBoundaryAcrossFacePolicies = refl

sameBoundaryDifferentStructuredState :
  expand originReciprocalPolicy selectedSeed
  ≡
  expand originUnderdeterminedPolicy selectedSeed
  →
  ⊥
sameBoundaryDifferentStructuredState equality
  with cong Cell.triadicFace equality
... | ()

expandCarryStep :
  {depth : Nat}
  {state : Cell.StructuredTrialecticState}
  {gluing : Cell.SecondOrderCellGluing state} →
  NextStructuredExpansionPolicy →
  CarryDepth.TrialecticCellCarryStep depth state gluing →
  Cell.StructuredTrialecticState
expandCarryStep policy step =
  expand policy (CarryDepth.nextDepthCell step)

expandedCarryStepEmbedsSeed :
  {depth : Nat}
  {state : Cell.StructuredTrialecticState}
  {gluing : Cell.SecondOrderCellGluing state} →
  (policy : NextStructuredExpansionPolicy) →
  (step : CarryDepth.TrialecticCellCarryStep depth state gluing) →
  Cell.leftCell
    (Cell.edgeAB
      (Cell.structuredBoundary (expandCarryStep policy step)))
  ≡ CarryDepth.nextDepthCell step
expandedCarryStepEmbedsSeed policy step =
  carriedSeedEmbeddedAtA policy (CarryDepth.nextDepthCell step)

data CarrySeedForcesUniqueStructuredExpansion : Set where
data OneExpansionPolicySuppliesAllDepthCoherence : Set where

carrySeedDoesNotForceUniqueStructuredExpansion :
  CarrySeedForcesUniqueStructuredExpansion → ⊥
carrySeedDoesNotForceUniqueStructuredExpansion ()

oneExpansionPolicyDoesNotProveAllDepthCoherence :
  OneExpansionPolicySuppliesAllDepthCoherence → ⊥
oneExpansionPolicyDoesNotProveAllDepthCoherence ()

record TrialecticCarryDepthExpansionPolicyBoundary : Set where
  constructor trialectic-carry-depth-expansion-policy-boundary
  field
    explicitExpansionPolicyConstructed : Bool
    carrySeedEmbeddedInExpandedBoundary : Bool
    sameSeedDistinctBoundaryExpansionsPaid : Bool
    sameBoundaryDistinctFaceExpansionsPaid : Bool
    carrySeedUniquelyDeterminesNextStructuredState : Bool
    allDepthCoherenceAutomatic : Bool
    expansionIsClaimedEmpiricalDynamics : Bool

open TrialecticCarryDepthExpansionPolicyBoundary public

canonicalTrialecticCarryDepthExpansionPolicyBoundary :
  TrialecticCarryDepthExpansionPolicyBoundary
canonicalTrialecticCarryDepthExpansionPolicyBoundary =
  trialectic-carry-depth-expansion-policy-boundary
    true true true true false false false
