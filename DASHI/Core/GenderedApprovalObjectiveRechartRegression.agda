module DASHI.Core.GenderedApprovalObjectiveRechartRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.GenderedApprovalObjectiveRechartExact as Rechart

changing-objective-can-change-choice :
  Rechart.chooseByObjective Rechart.approvalIndexedObjective
    ≡ Rechart.chooseByObjective Rechart.declaredCriterionObjective → ⊥
changing-objective-can-change-choice =
  Rechart.objectiveRechartChangesSelectedConduct

approval-independence-does-not-erase-sanctions :
  Rechart.approvalIndependenceEliminatesExternalSanction
    Rechart.canonicalApprovalObjectiveRechartBoundary ≡ false
approval-independence-does-not-erase-sanctions = refl

approval-independence-does-not-erase-desire :
  Rechart.approvalIndependenceEliminatesDesire
    Rechart.canonicalApprovalObjectiveRechartBoundary ≡ false
approval-independence-does-not-erase-desire = refl

reciprocal-relation-need-not-have-sovereign-evaluator :
  Rechart.reciprocalRelationRequiresSovereignEvaluator
    Rechart.canonicalApprovalObjectiveRechartBoundary ≡ false
reciprocal-relation-need-not-have-sovereign-evaluator = refl

relation-can-persist-after-rechart :
  Rechart.relationCanPersistWithoutOneCentredApprovalObjective
    Rechart.canonicalApprovalObjectiveRechartBoundary ≡ true
relation-can-persist-after-rechart = refl
