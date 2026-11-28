module DASHI.Governance.RelationalFederationOODALoopExact where

-- Thin composition of #697's history-indexed OODA spine and #1558's
-- scoped option cone. No semantic or political authority from a chart.
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Data.Empty using (⊥)
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Core.ProofExperimentAction369IntegrationExact as Integration
import DASHI.Core.SequentialRelationalExperimentPlannerExact as Experiment
import DASHI.Moonshine.Base369OODAProofExperimentObserverExact as Chart
import DASHI.Core.MarketMechanismProofExperimentActionCrossPollinationExact as Market
import DASHI.Reasoning.HistoryTimeIndexedAlgorithmModelExact as Model
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.RelationalFederationScopedViabilityExact as Scope
import DASHI.Governance.RelationalFederationSystemVOptionConeExact as Option

-- Consume canonical loop and chart boundaries rather than define a new OODA.
loopBoundary : Loop.ProofExperimentActionLoopBoundary
loopBoundary = Loop.canonicalProofExperimentActionLoopBoundary

chartBoundary : Chart.Base369OODAObserverBoundary
chartBoundary = Chart.canonicalBase369OODAObserverBoundary

marketBoundary : Market.MarketMechanismCrossPollinationBoundary
marketBoundary = Market.canonicalMarketMechanismCrossPollinationBoundary

-- Explicit live inhabitant: inconsistent/empty evidence cannot be accepted
-- as successful consumer closure by vacuous universal quantification.
InhabitedLive : Loop.LiveResidualFibre → Set
InhabitedLive f = Σ (Loop.Hypothesis f) (Loop.live f)

record NonemptyConsumerClosure (f : Loop.LiveResidualFibre) : Set₁ where
  field
    inhabitant : InhabitedLive f
    closure : Loop.ConsumerClosedAt f

refineFibre : (f : Loop.LiveResidualFibre) →
  (Loop.Hypothesis f → Set) → String → Loop.LiveResidualFibre
refineFibre f evidence ref = record
  { Hypothesis = Loop.Hypothesis f
  ; live = λ h → Loop.live f h × evidence h
  ; residualReference = ref
  ; consumerReference = Loop.consumerReference f
  }

refinementRetainsPrior :
  (f : Loop.LiveResidualFibre) (P : Loop.Hypothesis f → Set)
  (ref : String) → InhabitedLive (refineFibre f P ref) → InhabitedLive f
refinementRetainsPrior f P ref (h , old , new) = h , old

emptyExcludesClosure :
  {f : Loop.LiveResidualFibre} →
  (InhabitedLive f → ⊥) → NonemptyConsumerClosure f → ⊥
emptyExcludesClosure impossible receipt =
  impossible (NonemptyConsumerClosure.inhabitant receipt)

-- Existing consumer closure persists under a nonempty restriction with
-- the SAME consumer and hypothesis carrier; revised models need reaudit.
restrictClosure :
  (f : Loop.LiveResidualFibre) (P : Loop.Hypothesis f → Set)
  (ref : String) → Loop.ConsumerClosedAt f →
  InhabitedLive (refineFibre f P ref) →
  NonemptyConsumerClosure (refineFibre f P ref)
restrictClosure f P ref old nonempty = record
  { inhabitant = nonempty
  ; closure = record
    { Consumer = Loop.ConsumerClosedAt.Consumer old
    ; consumer = Loop.ConsumerClosedAt.consumer old
    ; constantOnLive = λ l r lp rp →
        Loop.ConsumerClosedAt.constantOnLive old l r (proj₁ lp) (proj₁ rp)
    ; closureReference = Loop.ConsumerClosedAt.closureReference old
    }
  }

-- Reuse set-valued predictions rather than force a deterministic sensor.
experimentRefinement :
  (f : Loop.LiveResidualFibre) {E O : Set} →
  Experiment.RelationalExperimentSystem (Loop.Hypothesis f) E O →
  E → O → String → Loop.LiveResidualFibre
experimentRefinement f system e o ref =
  refineFibre f (λ h → Experiment.predicts system h e o) ref

-- A candidate receipt's before and move must match the actual step.
-- Existing string references alone cannot prove these equalities.
record ExactFeedback (f : Loop.LiveResidualFibre)
  (move : Loop.CandidateMove f) : Set₁ where
  field
    next : Loop.LiveResidualFibre
    -- Construct the existing step from the exact before/move/after rather
    -- than try to equate a dependent move at unrelated before fibres.
    outcome : Loop.MoveOutcome
    observation orientation decision action feedback spine : String

asCyberneticStep :
  {f : Loop.LiveResidualFibre} {move : Loop.CandidateMove f} →
  ExactFeedback f move → Loop.CyberneticStep
asCyberneticStep {f} {move} r = record
  { before = f
  ; move = move
  ; after = ExactFeedback.next r
  ; outcome = ExactFeedback.outcome r
  ; observationReference = ExactFeedback.observation r
  ; orientationReference = ExactFeedback.orientation r
  ; decisionReference = ExactFeedback.decision r
  ; actionReference = ExactFeedback.action r
  ; feedbackReference = ExactFeedback.feedback r
  ; sameSpineReference = ExactFeedback.spine r
  }

-- Proof/observation/test/act are distinct; a test requires its own
-- externally supplied admission and cannot create a permanent mandate.
record GovernedTest (f : Loop.LiveResidualFibre)
  (move : Loop.CandidateMove f) (TestAuthority : Loop.CandidateMove f → Set)
  : Set₁ where
  field
    kindIsTest : Loop.kind move ≡ Loop.testMove
    admittedTest : TestAuthority move

-- Link the SAME OODA act to a governed option path. Binding is an explicit
-- external receipt; neither a string nor an observer sector can pay it.
record GovernedAct {State ScopeID : Set}
  {ts : Base.TransitionSystem State}
  {e : Scope.ScopedExtension State ScopeID}
  (c : Scope.ScopedStepContract ts e) (s : State)
  (f : Loop.LiveResidualFibre) (move : Loop.CandidateMove f)
  (candidate baseline : Option.CandidatePath c s)
  (M R B : Option.CandidatePath c s → Set)
  (C : Option.CandidatePath c s → Option.CandidatePath c s → Set)
  (Binding : Loop.CandidateMove f → Option.CandidatePath c s → Set)
  : Set₁ where
  field
    kindIsAct : Loop.kind move ≡ Loop.actMove
    pathBinding : Binding move candidate
    governed : Option.GovernedSelection c s M R B C candidate baseline

actTargetViable :
  ∀ {State ScopeID : Set} {ts : Base.TransitionSystem State}
    {e : Scope.ScopedExtension State ScopeID}
    {c : Scope.ScopedStepContract ts e} {s : State}
    {f : Loop.LiveResidualFibre} {move : Loop.CandidateMove f}
    {candidate baseline : Option.CandidatePath c s}
    {M R B : Option.CandidatePath c s → Set}
    {C : Option.CandidatePath c s → Option.CandidatePath c s → Set}
    {Binding : Loop.CandidateMove f → Option.CandidatePath c s → Set} →
  GovernedAct c s f move candidate baseline M R B C Binding →
  Scope.JointViable e (Option.CandidatePath.target candidate)
actTargetViable a = Option.selectedTargetViable (GovernedAct.governed a)

thinkIsNotAct : Loop.thinkMove ≡ Loop.actMove → ⊥
thinkIsNotAct ()

testIsNotAct : Loop.testMove ≡ Loop.actMove → ⊥
testIsNotAct ()

-- Preserve model/version identities separately from state refinement.
-- This aliases the actual owner, not a new history or revision ontology.
FrozenModel :
  (surface : Model.HistoryTimeAlgorithmModelSurface) →
  Model.History surface → Model.Time surface → Model.Time surface → Set₁
FrozenModel = Model.StateRefinementWithFrozenModel
