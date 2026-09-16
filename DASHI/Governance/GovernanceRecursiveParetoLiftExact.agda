module DASHI.Governance.GovernanceRecursiveParetoLiftExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RecursiveParetoFrontierLiftingExact as Recursive

------------------------------------------------------------------------
-- GOVERNANCE RECURSIVE PARETO LIFT
--
-- Preserve distinct local frontiers rather than flattening evidence acquisition,
-- observer refinement, policy routing, and transition dynamics into one cost
-- vector.  Each stage uses the canonical FrontierLift contract, which preserves
-- activity and all inherited axis costs while allowing new residual-relevant
-- axes to appear at the higher stage.
------------------------------------------------------------------------

record GovernanceParetoTower : Set₁ where
  constructor governanceParetoTower
  field
    evidenceLayer : Recursive.FrontierLayer
    observerLayer : Recursive.FrontierLayer
    policyLayer : Recursive.FrontierLayer
    transitionLayer : Recursive.FrontierLayer

    evidenceToObserver :
      Recursive.FrontierLift evidenceLayer observerLayer
    observerToPolicy :
      Recursive.FrontierLift observerLayer policyLayer
    policyToTransition :
      Recursive.FrontierLift policyLayer transitionLayer

    observerResidualMaterialisation :
      Recursive.ResidualRelevantMaterialisation evidenceToObserver
    policyResidualMaterialisation :
      Recursive.ResidualRelevantMaterialisation observerToPolicy
    transitionResidualMaterialisation :
      Recursive.ResidualRelevantMaterialisation policyToTransition

open GovernanceParetoTower public

liftEvidenceCandidateToTransition :
  (T : GovernanceParetoTower) →
  Recursive.Candidate (evidenceLayer T) →
  Recursive.Candidate (transitionLayer T)
liftEvidenceCandidateToTransition T candidate =
  Recursive.liftCandidate (policyToTransition T)
    (Recursive.liftCandidate (observerToPolicy T)
      (Recursive.liftCandidate (evidenceToObserver T) candidate))

liftEvidenceAxisToTransition :
  (T : GovernanceParetoTower) →
  Recursive.Axis (evidenceLayer T) →
  Recursive.Axis (transitionLayer T)
liftEvidenceAxisToTransition T axis =
  Recursive.embedAxis (policyToTransition T)
    (Recursive.embedAxis (observerToPolicy T)
      (Recursive.embedAxis (evidenceToObserver T) axis))

------------------------------------------------------------------------
-- Exact three-stage inherited-cost theorem.
------------------------------------------------------------------------

inheritedEvidenceCostPreservedAtTransition :
  (T : GovernanceParetoTower) →
  (axis : Recursive.Axis (evidenceLayer T)) →
  (candidate : Recursive.Candidate (evidenceLayer T)) →
  Recursive.cost (transitionLayer T)
    (liftEvidenceAxisToTransition T axis)
    (liftEvidenceCandidateToTransition T candidate)
  ≡ Recursive.cost (evidenceLayer T) axis candidate
inheritedEvidenceCostPreservedAtTransition T axis candidate
  rewrite Recursive.oldCostPreserved
    (policyToTransition T)
    (Recursive.embedAxis (observerToPolicy T)
      (Recursive.embedAxis (evidenceToObserver T) axis))
    (Recursive.liftCandidate (observerToPolicy T)
      (Recursive.liftCandidate (evidenceToObserver T) candidate))
        | Recursive.oldCostPreserved
    (observerToPolicy T)
    (Recursive.embedAxis (evidenceToObserver T) axis)
    (Recursive.liftCandidate (evidenceToObserver T) candidate)
        | Recursive.oldCostPreserved
    (evidenceToObserver T) axis candidate = refl

inheritedEvidenceActivityPreservedAtTransition :
  (T : GovernanceParetoTower) →
  (candidate : Recursive.Candidate (evidenceLayer T)) →
  Recursive.Active (evidenceLayer T) candidate →
  Recursive.Active (transitionLayer T)
    (liftEvidenceCandidateToTransition T candidate)
inheritedEvidenceActivityPreservedAtTransition T candidate active =
  Recursive.activePreserved (policyToTransition T)
    (Recursive.liftCandidate (observerToPolicy T)
      (Recursive.liftCandidate (evidenceToObserver T) candidate))
    (Recursive.activePreserved (observerToPolicy T)
      (Recursive.liftCandidate (evidenceToObserver T) candidate)
      (Recursive.activePreserved (evidenceToObserver T) candidate active))

------------------------------------------------------------------------
-- Old-axis dominance is preserved on the embedded old chart.  This deliberately
-- does NOT claim global Pareto dominance after new axes are materialised.
------------------------------------------------------------------------

EvidenceAxisDominates :
  (T : GovernanceParetoTower) →
  Recursive.Candidate (evidenceLayer T) →
  Recursive.Candidate (evidenceLayer T) → Set
EvidenceAxisDominates T left right =
  (axis : Recursive.Axis (evidenceLayer T)) →
  Recursive.cost (evidenceLayer T) axis left ≤
  Recursive.cost (evidenceLayer T) axis right

TransitionEmbeddedEvidenceAxisDominates :
  (T : GovernanceParetoTower) →
  Recursive.Candidate (evidenceLayer T) →
  Recursive.Candidate (evidenceLayer T) → Set
TransitionEmbeddedEvidenceAxisDominates T left right =
  (axis : Recursive.Axis (evidenceLayer T)) →
  Recursive.cost (transitionLayer T)
    (liftEvidenceAxisToTransition T axis)
    (liftEvidenceCandidateToTransition T left)
  ≤ Recursive.cost (transitionLayer T)
    (liftEvidenceAxisToTransition T axis)
    (liftEvidenceCandidateToTransition T right)

embeddedOldAxisDominancePreserved :
  (T : GovernanceParetoTower) →
  {left right : Recursive.Candidate (evidenceLayer T)} →
  EvidenceAxisDominates T left right →
  TransitionEmbeddedEvidenceAxisDominates T left right
embeddedOldAxisDominancePreserved T {left} {right} dominates axis
  rewrite inheritedEvidenceCostPreservedAtTransition T axis left
        | inheritedEvidenceCostPreservedAtTransition T axis right =
  dominates axis

record GovernanceRecursiveParetoLiftBoundary : Set where
  constructor governance-recursive-pareto-lift-boundary
  field
    evidenceObserverPolicyTransitionRemainDistinct : Bool
    inheritedAxesKeepTheirCosts : Bool
    inheritedActivityIsPreserved : Bool
    onlyResidualRelevantNewAxesNeedMaterialisation : Bool
    oldAxisDominanceAutomaticallyImpliesGlobalDominance : Bool
    recursiveLiftCreatesPolicyOrProofAuthority : Bool

canonicalGovernanceRecursiveParetoLiftBoundary :
  GovernanceRecursiveParetoLiftBoundary
canonicalGovernanceRecursiveParetoLiftBoundary =
  governance-recursive-pareto-lift-boundary
    true true true true false false
