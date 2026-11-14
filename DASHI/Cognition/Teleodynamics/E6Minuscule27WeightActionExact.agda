module DASHI.Cognition.Teleodynamics.E6Minuscule27WeightActionExact where

------------------------------------------------------------------------
-- EXECUTION-GRADE E6 MINUSCULE-27 WEIGHT / ACTION RECOGNITION
--
-- The existing E8 -> E6 x A2 root split gives six mixed 27-root fibres.  The
-- exact Python audit `scripts/check_e6_minuscule27_weight_action.py` selects one
-- A2-weight fibre, projects it orthogonally to the E6 subspace, and verifies:
--
-- * 27 distinct projected weights;
-- * common squared norm 16/3 in doubled-coordinate normalization;
-- * pairwise inner products 4/3 (216 pairs) and -8/3 (135 pairs);
-- * root-difference adjacency degree 16 at every weight;
-- * all 72 E6 root reflections preserve the selected fibre;
-- * projection intertwines those E8-root and E6-weight reflections;
-- * the induced action is transitive on all 27 weights;
-- * six independent reflected generators produce 51840 permutations.
--
-- This is the correct finite same-action target for the mixed 27.  It does not
-- identify the finite weight orbit with the 27-dimensional rational Albert
-- representation space, nor does Python execution count as Agda-kernel proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Cognition.Teleodynamics.E8ExceptionalBranchingBridgeExact as Branch
import DASHI.Cognition.Teleodynamics.AlbertE6WeightRoleCorrectionExact as Role

record E6Minuscule27ExecutionReceipt : Set where
  constructor receipt
  field
    e8RootCount : Nat
    e6RootCount : Nat
    a2RootCount : Nat
    mixedFibreCount : Nat
    rootsPerMixedFibre : Nat
    projectedWeightCount : Nat
    commonWeightNormNumeratorThirds : Nat
    highInnerProductPairCount : Nat
    lowInnerProductPairCount : Nat
    rootDifferenceDegree : Nat
    e6RootReflectionsPreserveSelectedFibre : Bool
    projectionIntertwinesAllE6RootReflections : Bool
    weightOrbitTransitive : Bool
    generatedPermutationGroupOrder : Nat
    pythonExactArithmeticAuditPassed : Bool
    pythonExecutionCountsAsAgdaKernelProof : Bool

open E6Minuscule27ExecutionReceipt public

canonicalExecutionReceipt : E6Minuscule27ExecutionReceipt
canonicalExecutionReceipt =
  receipt
    240 72 6 6 27 27 16 216 135 16
    true true true 51840 true false

record E6Minuscule27Boundary : Set where
  constructor boundary
  field
    mixedRootFibreCountPaid : Bool
    projectedWeightSetCountPaidAtExecutionGrade : Bool
    twoDistanceWeightGeometryPaidAtExecutionGrade : Bool
    rootDifferenceGraph16RegularPaidAtExecutionGrade : Bool
    allE6ReflectionsPreserveFibrePaidAtExecutionGrade : Bool
    fibreProjectionActionIntertwiningPaidAtExecutionGrade : Bool
    transitiveWeylActionPaidAtExecutionGrade : Bool
    generatedPermutationOrder51840PaidAtExecutionGrade : Bool
    weightOrbitIsAlbertCarrier : Bool
    e6RepresentationSpaceConstructedFromWeightOrbitHere : Bool
    exactAgdaWeightActionKernelReceiptObserved : Bool

open E6Minuscule27Boundary public

canonicalBoundary : E6Minuscule27Boundary
canonicalBoundary =
  boundary
    true true true true true true true true
    false false false

branchStillPaysTwentySeven :
  Branch.positiveFibreCount Branch.canonicalE8E6A2RootSplitReceipt ≡ 27
branchStillPaysTwentySeven = refl

roleCorrectionStillTargetsWeights :
  Role.e8MixedFibreTargetsWeightOrbit Role.canonicalRoleBoundary ≡ true
roleCorrectionStillTargetsWeights = refl
