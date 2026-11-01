module DASHI.Reasoning.AttractorAlignedBranchSelectionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Attractor-aligned branch management.
--
-- A live branch is not valuable merely because it remains feasible.  Its
-- marginal contribution also depends on directional drift, information gain,
-- servicing cost, diversion and pairwise interaction.  The finite model below
-- separates these coordinates and proves concrete counterexamples to the rule
-- "more live branches means a better reachable outcome".
------------------------------------------------------------------------

data Drift : Set where
  towardAttractor : Drift
  neutralDrift : Drift
  awayFromAttractor : Drift

data InformationValue : Set where
  noInformation : InformationValue
  usefulInformation : InformationValue

data ServiceLoad : Set where
  lowLoad : ServiceLoad
  highLoad : ServiceLoad

data Diversion : Set where
  noDiversion : Diversion
  divertsFlow : Diversion

data Basin : Set where
  desiredBasin : Basin
  blockedBasin : Basin
  trapBasin : Basin

data Branch : Set where
  directRoute : Branch
  exploratoryRoute : Branch
  duplicateBlockedRoute : Branch
  attractiveDeadEnd : Branch

branchDrift : Branch → Drift
branchDrift directRoute = towardAttractor
branchDrift exploratoryRoute = neutralDrift
branchDrift duplicateBlockedRoute = neutralDrift
branchDrift attractiveDeadEnd = awayFromAttractor

branchInformation : Branch → InformationValue
branchInformation directRoute = usefulInformation
branchInformation exploratoryRoute = usefulInformation
branchInformation duplicateBlockedRoute = noInformation
branchInformation attractiveDeadEnd = noInformation

branchLoad : Branch → ServiceLoad
branchLoad directRoute = lowLoad
branchLoad exploratoryRoute = lowLoad
branchLoad duplicateBlockedRoute = highLoad
branchLoad attractiveDeadEnd = highLoad

branchDiversion : Branch → Diversion
branchDiversion directRoute = noDiversion
branchDiversion exploratoryRoute = noDiversion
branchDiversion duplicateBlockedRoute = divertsFlow
branchDiversion attractiveDeadEnd = divertsFlow

reachableBasin : Branch → Basin
reachableBasin directRoute = desiredBasin
reachableBasin exploratoryRoute = blockedBasin
reachableBasin duplicateBlockedRoute = blockedBasin
reachableBasin attractiveDeadEnd = trapBasin

data MarginalDecision : Set where
  retainBranch : MarginalDecision
  pruneBranch : MarginalDecision

marginalDecision : Branch → MarginalDecision
marginalDecision directRoute = retainBranch
marginalDecision exploratoryRoute = retainBranch
marginalDecision duplicateBlockedRoute = pruneBranch
marginalDecision attractiveDeadEnd = pruneBranch

directRouteRetained : marginalDecision directRoute ≡ retainBranch
directRouteRetained = refl

explorationCanBeRetainedWithoutPositiveDrift :
  branchDrift exploratoryRoute ≡ neutralDrift
  × marginalDecision exploratoryRoute ≡ retainBranch
explorationCanBeRetainedWithoutPositiveDrift = refl , refl

highActivityCanMoveAwayFromAttractor :
  branchLoad attractiveDeadEnd ≡ highLoad
  × branchDrift attractiveDeadEnd ≡ awayFromAttractor
  × reachableBasin attractiveDeadEnd ≡ trapBasin
highActivityCanMoveAwayFromAttractor = refl , (refl , refl)

duplicateOptionsCanShareOneBlockedBasin :
  reachableBasin exploratoryRoute
  ≡ reachableBasin duplicateBlockedRoute
duplicateOptionsCanShareOneBlockedBasin = refl

nominallyDistinctBranchesNeedNotCreateDistinctBasins :
  exploratoryRoute ≡ duplicateBlockedRoute → ⊥
nominallyDistinctBranchesNeedNotCreateDistinctBasins ()

data Interaction : Set where
  reinforcing : Interaction
  independent : Interaction
  interfering : Interaction

branchInteraction : Branch → Branch → Interaction
branchInteraction directRoute exploratoryRoute = reinforcing
branchInteraction exploratoryRoute directRoute = reinforcing
branchInteraction directRoute duplicateBlockedRoute = interfering
branchInteraction duplicateBlockedRoute directRoute = interfering
branchInteraction directRoute attractiveDeadEnd = interfering
branchInteraction attractiveDeadEnd directRoute = interfering
branchInteraction first second = independent

usefulBranchesCanReinforce :
  branchInteraction directRoute exploratoryRoute ≡ reinforcing
usefulBranchesCanReinforce = refl

feasibleLookingBranchCanInterfereWithDirectRoute :
  branchInteraction directRoute duplicateBlockedRoute ≡ interfering
feasibleLookingBranchCanInterfereWithDirectRoute = refl

record BranchAssessment : Set where
  constructor branchAssessment
  field
    branch : Branch
    drift : Drift
    information : InformationValue
    load : ServiceLoad
    diversion : Diversion
    basin : Basin
    decision : MarginalDecision

open BranchAssessment public

assessBranch : Branch → BranchAssessment
assessBranch candidate =
  branchAssessment
    candidate
    (branchDrift candidate)
    (branchInformation candidate)
    (branchLoad candidate)
    (branchDiversion candidate)
    (reachableBasin candidate)
    (marginalDecision candidate)

record AttractorAlignedPolicy : Set where
  constructor attractorAlignedPolicy
  field
    assess : Branch → BranchAssessment
    interaction : Branch → Branch → Interaction
    retainedExplorationRequiresDirectProgress : Bool
    retainedExplorationRequiresDirectProgressIsFalse :
      retainedExplorationRequiresDirectProgress ≡ false
    allFeasibleBranchesMustRemainLive : Bool
    allFeasibleBranchesMustRemainLiveIsFalse :
      allFeasibleBranchesMustRemainLive ≡ false

canonicalAttractorAlignedPolicy : AttractorAlignedPolicy
canonicalAttractorAlignedPolicy =
  attractorAlignedPolicy
    assessBranch
    branchInteraction
    false refl
    false refl

------------------------------------------------------------------------
-- Exact finite core law:
--
-- adding the adverse branch increases nominal option count but contributes an
-- away-from-attractor route, high service load and diversion into a trap basin.
------------------------------------------------------------------------

record AdverseMarginalWitness : Set where
  constructor adverseMarginalWitness
  field
    addedBranch : Branch
    addedBranchIsDistinct : addedBranch ≡ directRoute → ⊥
    addedDrift : branchDrift addedBranch ≡ awayFromAttractor
    addedLoad : branchLoad addedBranch ≡ highLoad
    addedDiversion : branchDiversion addedBranch ≡ divertsFlow
    addedBasin : reachableBasin addedBranch ≡ trapBasin
    policyPrunesAddedBranch :
      marginalDecision addedBranch ≡ pruneBranch

moreOptionsCanWorsenReachableStructure : AdverseMarginalWitness
moreOptionsCanWorsenReachableStructure =
  adverseMarginalWitness
    attractiveDeadEnd
    (λ ())
    refl
    refl
    refl
    refl
    refl
