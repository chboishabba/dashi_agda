module DASHI.Culture.IntellectualReceptionContextAuthorisationSequentialExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.IntellectualReceptionContextIndexedAuthorisedStabiliserProofSearchExperimentExact as Context
import DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact as Stabiliser
import DASHI.Core.ExperimentalCoordinateDesignExact as Experiment
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis

------------------------------------------------------------------------
-- SEQUENTIAL AUTHORITY-STATUS EXPERIMENT
--
-- The active proof-search owners already establish the generic pattern
--
--   collision -> discriminator -> observation -> refined live fibre -> close
--
-- when the declared consumer becomes constant.  This file instantiates that
-- pattern on the reception stabiliser's authority residual.  The experiment
-- identifies the authority decision needed by the consumer; it does not create
-- the authority receipt itself.
------------------------------------------------------------------------

allAuthorityContextsLive : Context.ReceptionAuthorityContext → Set
allAuthorityContextsLive _ = ⊤

authorityObservationDeterminesDecision :
  (left right : Context.ReceptionAuthorityContext) →
  Context.authorityContextObservation left
  ≡ Context.authorityContextObservation right →
  Context.reflectionAuthorityDecision left
  ≡ Context.reflectionAuthorityDecision right
authorityObservationDeterminesDecision
  Context.baselineAuthorityContext Context.baselineAuthorityContext refl = refl
authorityObservationDeterminesDecision
  Context.baselineAuthorityContext Context.reviewedComparisonContext ()
authorityObservationDeterminesDecision
  Context.reviewedComparisonContext Context.baselineAuthorityContext ()
authorityObservationDeterminesDecision
  Context.reviewedComparisonContext Context.reviewedComparisonContext refl = refl

authorityOutcomeContinuation :
  (outcome : Context.StabiliserExperimentValue) →
  Planner.OutcomePossible
    allAuthorityContextsLive
    Context.authorityStatusBundle
    outcome →
  Planner.SequentialConsumerPlan
    Context.reflectionAuthorityDecision
    (Planner.RefineByBundle
      allAuthorityContextsLive
      Context.authorityStatusBundle
      outcome)
authorityOutcomeContinuation outcome possible =
  Planner.closeConsumer λ left right leftLive rightLive →
    authorityObservationDeterminesDecision
      left
      right
      (trans (proj₂ leftLive) (sym (proj₂ rightLive)))

authorityOneStepConsumerPlan :
  Planner.SequentialConsumerPlan
    Context.reflectionAuthorityDecision
    allAuthorityContextsLive
authorityOneStepConsumerPlan =
  Planner.askThen
    Context.authorityStatusBundle
    authorityOutcomeContinuation

------------------------------------------------------------------------
-- Exact finite outcome receipts: both current contexts are live possibilities.
------------------------------------------------------------------------

baselineOutcomePossible :
  Planner.OutcomePossible
    allAuthorityContextsLive
    Context.authorityStatusBundle
    Context.authorityMissingValue
baselineOutcomePossible =
  Context.baselineAuthorityContext , (tt , refl)

reviewedOutcomePossible :
  Planner.OutcomePossible
    allAuthorityContextsLive
    Context.authorityStatusBundle
    Context.authorityPresentValue
reviewedOutcomePossible =
  Context.reviewedComparisonContext , (tt , refl)

baselineOutcomeClosesBlockedDecision :
  Planner.SequentialConsumerPlan
    Context.reflectionAuthorityDecision
    (Planner.RefineByBundle
      allAuthorityContextsLive
      Context.authorityStatusBundle
      Context.authorityMissingValue)
baselineOutcomeClosesBlockedDecision =
  authorityOutcomeContinuation Context.authorityMissingValue baselineOutcomePossible

reviewedOutcomeClosesAuthorisedDecision :
  Planner.SequentialConsumerPlan
    Context.reflectionAuthorityDecision
    (Planner.RefineByBundle
      allAuthorityContextsLive
      Context.authorityStatusBundle
      Context.authorityPresentValue)
reviewedOutcomeClosesAuthorisedDecision =
  authorityOutcomeContinuation Context.authorityPresentValue reviewedOutcomePossible

------------------------------------------------------------------------
-- Proof search and sequential experiment can coexist while the baseline
-- governance authority remains absent.  This is the least-privilege point:
-- investigability is weaker than action authority.
------------------------------------------------------------------------

record InvestigableBeforeAuthorised : Set₁ where
  constructor investigable-before-authorised
  field
    semanticCandidate :
      Stabiliser.SemanticRolePreservingGenerator
        Stabiliser.comparisonFlipXGenerator
    liveProofSearch : ProofSearch.LiveProofSearch
    authorityExperiment :
      Planner.SequentialConsumerPlan
        Context.reflectionAuthorityDecision
        allAuthorityContextsLive
    baselineStillBlocked :
      Context.ContextAuthorisedGenerator
        Context.baselineAuthorityContext
        Stabiliser.comparisonFlipXGenerator → ⊥

open InvestigableBeforeAuthorised public

canonicalInvestigableBeforeAuthorised : InvestigableBeforeAuthorised
canonicalInvestigableBeforeAuthorised =
  investigable-before-authorised
    Stabiliser.semanticComparisonReflection
    Context.comparisonReflectionInvestigationIsLive
    authorityOneStepConsumerPlan
    Context.baselineComparisonReflectionNotAuthorised

------------------------------------------------------------------------
-- Existing boundaries retained literally.
------------------------------------------------------------------------

experimentalCoordinateBoundaryRetained : Experiment.ExperimentalCoordinateBoundary
experimentalCoordinateBoundaryRetained =
  Experiment.canonicalExperimentalCoordinateBoundary

proofSearchLeastPrivilegeBoundaryRetained :
  ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchLeastPrivilegeBoundaryRetained =
  ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

sequentialExperimentBoundaryRetained : Planner.SequentialExperimentPlannerBoundary
sequentialExperimentBoundaryRetained =
  Planner.canonicalSequentialExperimentPlannerBoundary

discriminatorSynthesisBoundaryRetained : Synthesis.DiscriminatorSynthesisBoundary
discriminatorSynthesisBoundaryRetained =
  Synthesis.canonicalDiscriminatorSynthesisBoundary

data ExperimentOutcomeCreatesScopedAuthority : Set where
data SearchClosureCreatesScopedAuthority : Set where
\data ConsumerClosureMeansWholeContextIdentity : Set where

experimentOutcomeDoesNotCreateScopedAuthority :
  ExperimentOutcomeCreatesScopedAuthority → ⊥
experimentOutcomeDoesNotCreateScopedAuthority ()

searchClosureDoesNotCreateScopedAuthority :
  SearchClosureCreatesScopedAuthority → ⊥
searchClosureDoesNotCreateScopedAuthority ()

consumerClosureDoesNotRequireWholeContextIdentity :
  ConsumerClosureMeansWholeContextIdentity → ⊥
consumerClosureDoesNotRequireWholeContextIdentity ()

record IntellectualReceptionContextAuthorisationSequentialExperimentBoundary : Set where
  constructor intellectual-reception-context-authorisation-sequential-experiment-boundary
  field
    authorityResidualHasOneStepConsumerPlan : Bool
    bothDeclaredAuthorityOutcomesAreLive : Bool
    proofSearchCanInvestigateBeforeGovernanceAuthority : Bool
    experimentOutcomeCreatesAuthority : Bool
    consumerClosureRequiresWholeWorldIdentity : Bool
    nextExperimentCouldBeOutcomeDependentInGeneralPlanner : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionContextAuthorisationSequentialExperimentBoundary :
  IntellectualReceptionContextAuthorisationSequentialExperimentBoundary
canonicalIntellectualReceptionContextAuthorisationSequentialExperimentBoundary =
  intellectual-reception-context-authorisation-sequential-experiment-boundary
    true true true false false true true
