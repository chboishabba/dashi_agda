module DASHI.Law.SensibLawConcreteDutyRefinementParetoRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawNegligenceDutyGenericParetoFrontierExact as DutyPareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment

------------------------------------------------------------------------
-- CONCRETE DUTY REFINEMENT -> PARETO RERUN
--
-- DASHI synthetic control-state fixture. The added proposition means only that
-- the core-government-policy coordinate has received an admitted assessment for
-- this scheduler state. It is not itself a court holding that the conduct is, or
-- is not, core government policy.
------------------------------------------------------------------------

emptyDutyGraph : Algebra.LegalGraph
emptyDutyGraph = Algebra.legal-graph [] []

corePolicyAssessmentClosed : Algebra.LegalProposition
corePolicyAssessmentClosed = Negligence.compileDutyIssue Climate.coreGovernmentPolicy

beforePolicyFacts : Algebra.FactSet
beforePolicyFacts = Algebra.fact-set []

afterPolicyFacts : Algebra.FactSet
afterPolicyFacts = Algebra.fact-set (corePolicyAssessmentClosed ∷ [])

emptyGraphPreserved : Refinement.GraphRefinement emptyDutyGraph emptyDutyGraph
emptyGraphPreserved = Refinement.graph-refinement
  (λ { () })
  (λ { () })
  "no legal rule added by the synthetic scheduler-state refinement"
  "no legal authority source added by the synthetic scheduler-state refinement"

policyFactRefinement : Refinement.FactRefinement beforePolicyFacts afterPolicyFacts
policyFactRefinement = Refinement.fact-refinement
  (λ { () })
  "scheduler-state fact: core-government-policy coordinate assessed/closed"

policyAssessmentRefinementReceipt :
  Refinement.LegalRefinementReceipt
    emptyDutyGraph emptyDutyGraph beforePolicyFacts afterPolicyFacts
policyAssessmentRefinementReceipt = Refinement.legal-refinement-receipt
  emptyGraphPreserved
  policyFactRefinement
  Residual.missingInstitutionalConstraint
  Residual.inspectJudicialReasons
  Refinement.factCarrier
  true refl
  true refl

policyClosureFactPresent :
  Algebra._∈_ corePolicyAssessmentClosed (Algebra.facts afterPolicyFacts)
policyClosureFactPresent = Algebra.here

------------------------------------------------------------------------
-- The assessed result does not stop the legal research loop: it narrows the
-- live duty fibre and therefore demands a fresh Pareto computation.
------------------------------------------------------------------------

policyAssessmentFeedback :
  Feedback.feedbackDisposition
    Assessment.proofPaymentAdmitted
    Assessment.frontierNarrowed
  ≡ Feedback.recomputeFrontier
policyAssessmentFeedback = refl

frontierBeforePolicyAssessment :
  Pareto.paretoFrontier DutyPareto.currentDutyPortfolio
  ≡ DutyPareto.currentCorePolicyCell ∷ []
frontierBeforePolicyAssessment = DutyPareto.currentDutyParetoFrontierIsCorePolicyOnly

frontierAfterPolicyAssessment :
  Pareto.paretoFrontier DutyPareto.postPolicyPortfolio
  ≡ DutyPareto.postPolicyStatutoryCoherenceCell ∷ []
frontierAfterPolicyAssessment = DutyPareto.postPolicyParetoFrontierIsStatutoryCoherenceOnly

selectedRequirementChanges :
  Pareto.requirement DutyPareto.currentCorePolicyCell
  ≡ Pareto.requirement DutyPareto.postPolicyStatutoryCoherenceCell
  → ⊥
selectedRequirementChanges ()

------------------------------------------------------------------------
-- Same-object transition receipt: one concrete fact-carrier refinement is paired
-- with the exact before/after scheduler frontiers. The frontier transition is a
-- consequence of recomputing the declared live-fibre portfolio, not a claim that
-- adding a fact definitionally rewrites legal doctrine.
------------------------------------------------------------------------

record ConcreteDutyResearchRerun : Set where
  constructor concrete-duty-research-rerun
  field
    refinementReceipt :
      Refinement.LegalRefinementReceipt
        emptyDutyGraph emptyDutyGraph beforePolicyFacts afterPolicyFacts
    admittedAssessmentRecomputes :
      Feedback.feedbackDisposition
        Assessment.proofPaymentAdmitted
        Assessment.frontierNarrowed
      ≡ Feedback.recomputeFrontier
    oldFrontier :
      Pareto.paretoFrontier DutyPareto.currentDutyPortfolio
      ≡ DutyPareto.currentCorePolicyCell ∷ []
    newFrontier :
      Pareto.paretoFrontier DutyPareto.postPolicyPortfolio
      ≡ DutyPareto.postPolicyStatutoryCoherenceCell ∷ []
    newStateCarriesClosedCoordinate :
      Algebra._∈_ corePolicyAssessmentClosed (Algebra.facts afterPolicyFacts)
    selectedCoordinatesAreDistinct :
      Pareto.requirement DutyPareto.currentCorePolicyCell
      ≡ Pareto.requirement DutyPareto.postPolicyStatutoryCoherenceCell
      → ⊥

open ConcreteDutyResearchRerun public

concreteDutyResearchRerun : ConcreteDutyResearchRerun
concreteDutyResearchRerun = concrete-duty-research-rerun
  policyAssessmentRefinementReceipt
  policyAssessmentFeedback
  frontierBeforePolicyAssessment
  frontierAfterPolicyAssessment
  policyClosureFactPresent
  selectedRequirementChanges

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SchedulerStateFactIsJudicialHolding : Set where
data FactRefinementAutomaticallyChangesDoctrine : Set where
data RecomputedFrontierPaysStatutoryCoherence : Set where

schedulerStateDoesNotBecomeHolding : SchedulerStateFactIsJudicialHolding → ⊥
schedulerStateDoesNotBecomeHolding ()

factRefinementDoesNotDefinitionallyRewriteDoctrine :
  FactRefinementAutomaticallyChangesDoctrine → ⊥
factRefinementDoesNotDefinitionallyRewriteDoctrine ()

newFrontierStillDoesNotPayNextRequirement :
  RecomputedFrontierPaysStatutoryCoherence → ⊥
newFrontierStillDoesNotPayNextRequirement ()
