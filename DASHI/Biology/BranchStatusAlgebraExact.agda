module DASHI.Biology.BranchStatusAlgebraExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- PHYSICAL POSSIBILITY / PREDICTED WEIGHT / ACCESS / BARRIER / ACTIONABILITY
-- ARE DISTINCT COORDINATES OF A FUTURE BRANCH.
------------------------------------------------------------------------

record BranchProfile : Set where
  constructor branchProfile
  field
    physicalPossible : Bool
    predictedWeight : Nat
    accessible : Bool
    barrier : Nat
    actionable : Bool

open BranchProfile public

baselineBranch : BranchProfile
baselineBranch = branchProfile true 3 true 1 true

sameWeightAccessible : BranchProfile
sameWeightAccessible = branchProfile true 2 true 1 true

sameWeightGated : BranchProfile
sameWeightGated = branchProfile true 2 false 1 false

sameAccessLowWeight : BranchProfile
sameAccessLowWeight = branchProfile true 1 true 1 true

sameAccessHighWeight : BranchProfile
sameAccessHighWeight = branchProfile true 3 true 1 true

samePredictedWeightDifferentAccessibility :
  predictedWeight sameWeightAccessible ≡ predictedWeight sameWeightGated
samePredictedWeightDifferentAccessibility = refl

accessibilityStillDiffersAtSameWeight :
  sameWeightAccessible ≡ sameWeightGated → ⊥
accessibilityStillDiffersAtSameWeight ()

sameAccessibilityDifferentPredictedWeight :
  accessible sameAccessLowWeight ≡ accessible sameAccessHighWeight
sameAccessibilityDifferentPredictedWeight = refl

weightStillDiffersAtSameAccessibility :
  sameAccessLowWeight ≡ sameAccessHighWeight → ⊥
weightStillDiffersAtSameAccessibility ()

prune : BranchProfile → BranchProfile
prune profile =
  branchProfile
    (physicalPossible profile)
    (predictedWeight profile)
    false
    (barrier profile)
    false

reweight : Nat → BranchProfile → BranchProfile
reweight weight profile =
  branchProfile
    (physicalPossible profile)
    weight
    (accessible profile)
    (barrier profile)
    (actionable profile)

raiseBarrier : Nat → BranchProfile → BranchProfile
raiseBarrier height profile =
  branchProfile
    (physicalPossible profile)
    (predictedWeight profile)
    (accessible profile)
    height
    (actionable profile)

loseActuation : BranchProfile → BranchProfile
loseActuation profile =
  branchProfile
    (physicalPossible profile)
    (predictedWeight profile)
    (accessible profile)
    (barrier profile)
    false

pruningDoesNotDeletePhysicalPossibility :
  physicalPossible (prune baselineBranch) ≡ physicalPossible baselineBranch
pruningDoesNotDeletePhysicalPossibility = refl

pruningDiffersFromReweighting :
  prune baselineBranch ≡ reweight 1 baselineBranch → ⊥
pruningDiffersFromReweighting ()

barrierRaiseDiffersFromActuationLoss :
  raiseBarrier 3 baselineBranch ≡ loseActuation baselineBranch → ⊥
barrierRaiseDiffersFromActuationLoss ()

accessibleButNonActionable : BranchProfile
accessibleButNonActionable = loseActuation baselineBranch

accessDoesNotImplyActuation :
  accessible accessibleButNonActionable ≡ actionable accessibleButNonActionable → ⊥
accessDoesNotImplyActuation ()

record BranchStatusBoundary : Set where
  constructor branchStatusBoundary
  field
    possibilityEqualsProbability : Bool
    probabilityEqualsAccessibility : Bool
    accessibilityEqualsActionability : Bool
    pruningEqualsDeletionFromWorldCarrier : Bool
    highBarrierEqualsInaccessibility : Bool

canonicalBranchStatusBoundary : BranchStatusBoundary
canonicalBranchStatusBoundary =
  branchStatusBoundary false false false false false
