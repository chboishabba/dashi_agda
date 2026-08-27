module DASHI.Governance.TypedBranchingOptionConeBridgeExact where

------------------------------------------------------------------------
-- TYPED BRANCHING / REACHABILITY -> OPTION-CONE BRIDGE
--
-- SOURCE / OWNER LINEAGE
--
-- Theodore E. Harris,
-- "The Theory of Branching Processes", Springer, 1963.
-- DOI: 10.1007/978-3-642-51866-9.
--
-- E. Seneta,
-- "Non-negative Matrices and Markov Chains", 2nd ed., Springer, 1981.
-- DOI: 10.1007/0-387-32792-4.
--
-- The branching/reachability mathematics is owned by
-- `FiniteTypedBranchingReachabilityBridgeExact`.  The proof-bearing option-cone
-- interface is owned by `OptionConeCoercionExact`.  This module adds only the
-- adapter between those existing theorem families.
--
-- The central exact witness is:
--
--   equal local row mass / equal row regime
--   + different target reachability
--   -> different reachable option cone.
--
-- No empirical coercion, welfare, social-policy, psychological or demographic
-- conclusion is inferred from this finite bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥-elim)

import DASHI.Core.FiniteTypedBranchingKernelExact as Kernel
import DASHI.Core.FiniteTypedBranchingReachabilityBridgeExact as Branch
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Governance.OptionConeCoercionExact as Cone

------------------------------------------------------------------------
-- One declared long-horizon option: reaching the canonical escape goal.
------------------------------------------------------------------------

data GoalOption : Set where
  reachEscapeGoal : GoalOption

ReachableGoal : Branch.RouteType → GoalOption → Set
ReachableGoal state reachEscapeGoal =
  Reach.Reachable Branch.routeSystem state Branch.escapeGoal

branchGoalCone : Cone.SafeReachabilitySystem Branch.RouteType GoalOption
branchGoalCone = Cone.safeReachabilitySystem ReachableGoal

goalAvailableFromEscapeStart :
  Cone.Available branchGoalCone Branch.escapeStart reachEscapeGoal
goalAvailableFromEscapeStart = Branch.escapeStartReachesGoal

goalUnavailableFromTrapStart :
  Cone.Available branchGoalCone Branch.trapStart reachEscapeGoal → ⊥
goalUnavailableFromTrapStart = Branch.trapStartCannotReachGoal

------------------------------------------------------------------------
-- Exact cone contraction as a comparison of the two start states.
--
-- `StrictSafeReachabilityContraction` itself does not assert that the second
-- state is the dynamical successor of the first; it compares their available
-- option sets.  We preserve that distinction here.
------------------------------------------------------------------------

trapConeIncludedInEscapeCone :
  (option : GoalOption) →
  Cone.Available branchGoalCone Branch.trapStart option →
  Cone.Available branchGoalCone Branch.escapeStart option
trapConeIncludedInEscapeCone reachEscapeGoal trappedAvailable =
  ⊥-elim (goalUnavailableFromTrapStart trappedAvailable)

canonicalBranchGoalConeContraction :
  Cone.StrictSafeReachabilityContraction
    branchGoalCone
    Branch.escapeStart
    Branch.trapStart
canonicalBranchGoalConeContraction =
  Cone.strictSafeReachabilityContraction
    trapConeIncludedInEscapeCone
    reachEscapeGoal
    goalAvailableFromEscapeStart
    goalUnavailableFromTrapStart

------------------------------------------------------------------------
-- Same local branch-count observer, different long-horizon option cone.
------------------------------------------------------------------------

sameLocalBranchMass :
  Kernel.rowScaledMass Branch.routeKernel Branch.escapeStart
  ≡ Kernel.rowScaledMass Branch.routeKernel Branch.trapStart
sameLocalBranchMass = refl

record EqualLocalMassDifferentOptionCone : Set₁ where
  constructor equal-local-mass-different-option-cone
  field
    sameMass :
      Kernel.rowScaledMass Branch.routeKernel Branch.escapeStart
      ≡ Kernel.rowScaledMass Branch.routeKernel Branch.trapStart
    availableOnEscapeSide :
      Cone.Available branchGoalCone Branch.escapeStart reachEscapeGoal
    unavailableOnTrapSide :
      Cone.Available branchGoalCone Branch.trapStart reachEscapeGoal → ⊥
    coneContraction :
      Cone.StrictSafeReachabilityContraction
        branchGoalCone Branch.escapeStart Branch.trapStart

canonicalEqualLocalMassDifferentOptionCone :
  EqualLocalMassDifferentOptionCone
canonicalEqualLocalMassDifferentOptionCone =
  equal-local-mass-different-option-cone
    sameLocalBranchMass
    goalAvailableFromEscapeStart
    goalUnavailableFromTrapStart
    canonicalBranchGoalConeContraction

record TypedBranchingOptionConeBoundary : Set where
  constructor typed-branching-option-cone-boundary
  field
    equalBranchMassImpliesEqualOptionCone : Bool
    equalBranchMassImpliesEqualOptionConeIsFalse :
      equalBranchMassImpliesEqualOptionCone ≡ false
    coneContractionAloneProvesCoercion : Bool
    coneContractionAloneProvesCoercionIsFalse :
      coneContractionAloneProvesCoercion ≡ false
    comparisonContractionClaimsActualStateTransition : Bool
    comparisonContractionClaimsActualStateTransitionIsFalse :
      comparisonContractionClaimsActualStateTransition ≡ false

canonicalTypedBranchingOptionConeBoundary : TypedBranchingOptionConeBoundary
canonicalTypedBranchingOptionConeBoundary =
  typed-branching-option-cone-boundary
    false refl
    false refl
    false refl
