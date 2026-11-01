module DASHI.Biology.Morphogenesis.RegenerativeRepairBoundary where

-- Regeneration is target-relative repair under perturbation, resources, and a
-- declared controllable disturbance class.  It is stronger than persistence and
-- weaker than a universal organism-independent repair theorem.
record RegenerativeRepairSystem : Set₁ where
  field
    TissueState  : Set
    Morphology   : Set
    Environment  : Set
    Perturbation : Set
    RepairAction : Set
    Resource     : Set
    Defect       : Set

    morphology : TissueState → Morphology
    perturb    : Perturbation → TissueState → TissueState
    repair     : Environment → Resource → RepairAction → TissueState → TissueState
    defect     : Morphology → TissueState → Defect

    LowerDefect : Defect → Defect → Set
    ResourceAvailable : Resource → TissueState → Set
    ActionAdmissible   : RepairAction → TissueState → Set

record RegenerativeRepairWitness
  (R : RegenerativeRepairSystem) : Set₁ where
  open RegenerativeRepairSystem R
  field
    environment  : Environment
    resource     : Resource
    initial      : TissueState
    target       : Morphology
    perturbation : Perturbation
    action       : RepairAction

    resourcesAvailable : ResourceAvailable resource (perturb perturbation initial)
    actionAdmissible : ActionAdmissible action (perturb perturbation initial)

    decreasesDefect :
      LowerDefect
        (defect target
          (repair environment resource action (perturb perturbation initial)))
        (defect target (perturb perturbation initial))

record RegenerativeBranchControl
  (R : RegenerativeRepairSystem) : Set₁ where
  open RegenerativeRepairSystem R
  field
    RepairBranch FailureBranch ScarBranch : Set
    BranchFor : Perturbation → Set

    admittedRepairBranch :
      (p : Perturbation) → BranchFor p → Set

-- Cancer, scarring, ageing, and failed repair may be represented as competing
-- multiscale branches, but none is definitionally reduced to one bioelectric or
-- genetic mechanism.
record RegenerativeAuthorityBoundary : Set₁ where
  field
    repairModelIsNotUniversalRegeneration : Set
    bioelectricDissociationIsNotSoleCancerCause : Set
    animalModelIsNotHumanTherapyAuthority : Set
    defectDecreaseIsNotCompleteFunctionalRecovery : Set
