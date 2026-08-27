module DASHI.Biology.EmbodiedBranchingHyperformalismExact where

open import DASHI.Core.Prelude

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Body
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Subfabric
import DASHI.Biology.TwoBoundaryHyperformalismExact as Two

------------------------------------------------------------------------
-- BRANCHING EMBODIED SUBFABRIC
--
-- Mathematical/interpretive precedents kept at the claim boundary:
--
-- Hugh Everett III,
-- "\"Relative State\" Formulation of Quantum Mechanics",
-- Reviews of Modern Physics 29 (1957), 454-462.
-- DOI: 10.1103/RevModPhys.29.454
--
-- Murray Gell-Mann, James B. Hartle,
-- "Classical Equations for Quantum Systems",
-- Physical Review D 47 (1993), 3345.
-- DOI: 10.1103/PhysRevD.47.3345
--
-- The finite DASHI object below is a branching family of possible embodied
-- continuations.  It is not a claim that Everettian worlds are physically real
-- or that neural dynamics are quantum decoherent histories.
------------------------------------------------------------------------

data BranchStatus : Set where
  liveBranch reweightedBranch highBarrierBranch gatedBranch : BranchStatus

statusNotCollapsed :
  liveBranch ≡ gatedBranch → ⊥
statusNotCollapsed ()

data HistoryToken : Set where retainedHistory : HistoryToken

data WorldSurface : Set where sameExternalWorld : WorldSurface

data GoalSurface : Set where sameSafetyGoal : GoalSurface

record EmbodiedBranchState : Set where
  constructor embodiedBranchState
  field
    world : WorldSurface
    goal : GoalSurface
    history : HistoryToken
    bodyContext : Subfabric.BodyContext

open EmbodiedBranchState public

regulatedBranchState : EmbodiedBranchState
regulatedBranchState =
  embodiedBranchState
    sameExternalWorld sameSafetyGoal retainedHistory Subfabric.regulatedContext

mobilisedBranchState : EmbodiedBranchState
mobilisedBranchState =
  embodiedBranchState
    sameExternalWorld sameSafetyGoal retainedHistory Subfabric.mobilisedContext

sameWorld :
  world regulatedBranchState ≡ world mobilisedBranchState
sameWorld = refl

sameGoal :
  goal regulatedBranchState ≡ goal mobilisedBranchState
sameGoal = refl

sameHistory :
  history regulatedBranchState ≡ history mobilisedBranchState
sameHistory = refl

accessiblePlanning :
  EmbodiedBranchState → Bool
accessiblePlanning state =
  Subfabric.live
    Subfabric.accessibleLayer
    (bodyContext state)
    Subfabric.flexiblePlanning

sameWorldGoalHistoryDifferentAccessibleFuture :
  accessiblePlanning regulatedBranchState
  ≡ accessiblePlanning mobilisedBranchState → ⊥
sameWorldGoalHistoryDifferentAccessibleFuture ()

feltState : EmbodiedBranchState → Body.FeltState
feltState state with bodyContext state
... | Subfabric.regulatedContext =
  Body.inferFeltState Body.safetyPrior (Body.afference Body.regulatedBody)
... | Subfabric.mobilisedContext =
  Body.inferFeltState Body.threatPrior (Body.afference Body.mobilisedBody)

sameWorldGoalHistoryDifferentFeltState :
  feltState regulatedBranchState ≡ feltState mobilisedBranchState → ⊥
sameWorldGoalHistoryDifferentFeltState ()

effectiveViableBranchCount :
  EmbodiedBranchState → Nat
effectiveViableBranchCount state with bodyContext state
... | Subfabric.regulatedContext = 3
... | Subfabric.mobilisedContext = 1

regulatedHasThreeEffectiveViableBranches :
  effectiveViableBranchCount regulatedBranchState ≡ 3
regulatedHasThreeEffectiveViableBranches = refl

mobilisedHasOneEffectiveViableBranch :
  effectiveViableBranchCount mobilisedBranchState ≡ 1
mobilisedHasOneEffectiveViableBranch = refl

branchCountContractionWitness :
  effectiveViableBranchCount regulatedBranchState
  ≡ effectiveViableBranchCount mobilisedBranchState → ⊥
branchCountContractionWitness ()

------------------------------------------------------------------------
-- Recovery can re-open the effective descendant subfabric while retaining the
-- history token.
------------------------------------------------------------------------

recover : EmbodiedBranchState → EmbodiedBranchState
recover state =
  embodiedBranchState
    (world state)
    (goal state)
    (history state)
    Subfabric.regulatedContext

recoveryPreservesHistory :
  (state : EmbodiedBranchState) →
  history (recover state) ≡ history state
recoveryPreservesHistory state = refl

recoveryReopensPlanning :
  accessiblePlanning (recover mobilisedBranchState) ≡ true
recoveryReopensPlanning = refl

twoBoundaryDiamondRetained :
  Two.Reach Two.startCell Two.goalCell
twoBoundaryDiamondRetained = Two.safePath

record BranchingHyperformalismBoundary : Set where
  constructor branchingHyperformalismBoundary
  field
    branchingMeansLiteralEverettWorlds : Bool
    physicalPossibilityEqualsAccessibility : Bool
    pruningEqualsReweighting : Bool
    recoveryRequiresHistoryErasure : Bool
    sameWorldGoalHistoryFixesFeltFuture : Bool

canonicalBranchingHyperformalismBoundary : BranchingHyperformalismBoundary
canonicalBranchingHyperformalismBoundary =
  branchingHyperformalismBoundary false false false false false
