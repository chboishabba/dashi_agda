module DASHI.Governance.InstitutionalNoticeActuationCulpabilityExact where

------------------------------------------------------------------------
-- INSTITUTIONAL NOTICE / ACTUATION / CULPABILITY
--
-- Thin legal-epistemic specialization over existing DASHI observer, Pareto,
-- contestability and option-cone theorem owners.  It formalizes the generic
-- structure discussed for self-represented institutional users without making
-- any empirical finding about a named litigant, tribunal or case.
--
-- Core separation:
--   coarse live fibre != wrong proposition;
--   delivery/repetition != decision-relevant refinement;
--   diagnostic interaction != closure;
--   AI actuation expansion != observer refinement;
--   reference-observer attribution != actual subject capability;
--   formal access != affordable refinement;
--   equal formal rights != equal effective capability;
--   same monetary sanction != same downstream harm;
--   culpability requires decision-safe refinement + accessible closure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Governance.ContestabilityAccessCostExact as Contestability
import DASHI.Governance.OptionConeCoercionExact as OptionCone

------------------------------------------------------------------------
-- 1. Fine legal state and observer fibres.
------------------------------------------------------------------------

data FineLegalState : Set where
  fatalThresholdState : FineLegalState
  viableSavingBranchState : FineLegalState
  wrongFactualTypingState : FineLegalState

data LegalDecision : Set where
  withdrawDecision persistDecision : LegalDecision

decision : FineLegalState → LegalDecision
decision fatalThresholdState = withdrawDecision
decision viableSavingBranchState = persistDecision
decision wrongFactualTypingState = persistDecision

data CoarseObservation : Set where
  threeDaysShortObservation : CoarseObservation

data DiagnosticObservation : Set where
  jurisdictionQuestionObservation factualTypingQuestionObservation :
    DiagnosticObservation

data FineObservation : Set where
  fatalObservation savingBranchObservation wrongTypingObservation : FineObservation

layObserver : Observer.Observer FineLegalState CoarseObservation
layObserver _ = threeDaysShortObservation

diagnosticObserver : Observer.Observer FineLegalState DiagnosticObservation
diagnosticObserver fatalThresholdState = jurisdictionQuestionObservation
diagnosticObserver viableSavingBranchState = jurisdictionQuestionObservation
diagnosticObserver wrongFactualTypingState = factualTypingQuestionObservation

expertObserver : Observer.Observer FineLegalState FineObservation
expertObserver fatalThresholdState = fatalObservation
expertObserver viableSavingBranchState = savingBranchObservation
expertObserver wrongFactualTypingState = wrongTypingObservation

DecisionSafe :
  ∀ {Observation : Set} →
  Observer.Observer FineLegalState Observation → Set
DecisionSafe observe =
  ∀ x y → observe x ≡ observe y → decision x ≡ decision y

layObserverIsNotDecisionSafe : DecisionSafe layObserver → ⊥
layObserverIsNotDecisionSafe safe with
  safe fatalThresholdState viableSavingBranchState refl
... | ()

diagnosticObserverIsNotDecisionSafe : DecisionSafe diagnosticObserver → ⊥
diagnosticObserverIsNotDecisionSafe safe with
  safe fatalThresholdState viableSavingBranchState refl
... | ()

expertObserverIsDecisionSafe : DecisionSafe expertObserver
expertObserverIsDecisionSafe fatalThresholdState fatalThresholdState equality = refl
expertObserverIsDecisionSafe fatalThresholdState viableSavingBranchState ()
expertObserverIsDecisionSafe fatalThresholdState wrongFactualTypingState ()
expertObserverIsDecisionSafe viableSavingBranchState fatalThresholdState ()
expertObserverIsDecisionSafe viableSavingBranchState viableSavingBranchState equality = refl
expertObserverIsDecisionSafe viableSavingBranchState wrongFactualTypingState ()
expertObserverIsDecisionSafe wrongFactualTypingState fatalThresholdState ()
expertObserverIsDecisionSafe wrongFactualTypingState viableSavingBranchState ()
expertObserverIsDecisionSafe wrongFactualTypingState wrongFactualTypingState equality = refl

layToDiagnosticStrictRefinement :
  Observer.StrictRefinement layObserver diagnosticObserver
layToDiagnosticStrictRefinement =
  Observer.strictRefinement
    (λ x y equality → refl)
    fatalThresholdState
    wrongFactualTypingState
    refl
    (λ ())

diagnosticToExpertStrictRefinement :
  Observer.StrictRefinement diagnosticObserver expertObserver
diagnosticToExpertStrictRefinement =
  Observer.strictRefinement
    (λ { fatalThresholdState fatalThresholdState equality → refl
       ; fatalThresholdState viableSavingBranchState ()
       ; fatalThresholdState wrongFactualTypingState ()
       ; viableSavingBranchState fatalThresholdState ()
       ; viableSavingBranchState viableSavingBranchState equality → refl
       ; viableSavingBranchState wrongFactualTypingState ()
       ; wrongFactualTypingState fatalThresholdState ()
       ; wrongFactualTypingState viableSavingBranchState ()
       ; wrongFactualTypingState wrongFactualTypingState equality → refl })
    fatalThresholdState
    viableSavingBranchState
    refl
    (λ ())

------------------------------------------------------------------------
-- 2. Folk observer / expert refinement / purchased access.
------------------------------------------------------------------------

data FolkFormationSource : Set where
  familySource schoolSource communitySource mediaSource workplaceSource
  policeSource popularLegalCultureSource priorInstitutionSource :
    FolkFormationSource

canonicalFolkFormationSources : List FolkFormationSource
canonicalFolkFormationSources =
  familySource ∷ schoolSource ∷ communitySource ∷ mediaSource
  ∷ workplaceSource ∷ policeSource ∷ popularLegalCultureSource
  ∷ priorInstitutionSource ∷ []

record HistoricallyProducedFolkObserver : Set where
  constructor historicallyProducedFolkObserver
  field
    observer : Observer.Observer FineLegalState CoarseObservation
    formationSources : List FolkFormationSource
    authoritativeRefinementExternallyControlled : Bool

canonicalHistoricallyProducedFolkObserver : HistoricallyProducedFolkObserver
canonicalHistoricallyProducedFolkObserver =
  historicallyProducedFolkObserver layObserver canonicalFolkFormationSources true

record PurchasedRefinement : Set where
  constructor purchasedRefinement
  field
    refinedObserver : Observer.Observer FineLegalState FineObservation
    advicePrice : Nat
    refinedObserverDecisionSafe : DecisionSafe refinedObserver

canonicalPurchasedRefinement : PurchasedRefinement
canonicalPurchasedRefinement =
  purchasedRefinement expertObserver 5 expertObserverIsDecisionSafe

formalContestabilityDoesNotImplyAffordableRefinement :
  Contestability.AffordableContestability
    Contestability.finiteCost
    Contestability.finiteBudget →
  ⊥
formalContestabilityDoesNotImplyAffordableRefinement =
  Contestability.formalAvailabilityDoesNotEstablishAffordability

------------------------------------------------------------------------
-- 3. AI changes reachable action more than observer resolution.
------------------------------------------------------------------------

data LegalAction : Set where
  withdrawAction seekAdviceAction generateSubmissionAction persistAction :
    LegalAction

data ReachableWithoutAI : LegalAction → Set where
  unaidedWithdraw : ReachableWithoutAI withdrawAction
  unaidedSeekAdvice : ReachableWithoutAI seekAdviceAction

data ReachableWithAI : LegalAction → Set where
  aiWithdraw : ReachableWithAI withdrawAction
  aiSeekAdvice : ReachableWithAI seekAdviceAction
  aiGenerateSubmission : ReachableWithAI generateSubmissionAction
  aiPersist : ReachableWithAI persistAction

unaidedActionsRemainAIReachable :
  (action : LegalAction) → ReachableWithoutAI action → ReachableWithAI action
unaidedActionsRemainAIReachable withdrawAction unaidedWithdraw = aiWithdraw
unaidedActionsRemainAIReachable seekAdviceAction unaidedSeekAdvice = aiSeekAdvice

aiSubmissionWasNotUnaidedReachable :
  ReachableWithoutAI generateSubmissionAction → ⊥
aiSubmissionWasNotUnaidedReachable ()

record StrictActuationExpansion : Set where
  constructor strictActuationExpansion
  field
    inclusion :
      (action : LegalAction) → ReachableWithoutAI action → ReachableWithAI action
    newlyReachable : LegalAction
    newlyReachableAfterAI : ReachableWithAI newlyReachable
    newlyReachableBeforeAIImpossible : ReachableWithoutAI newlyReachable → ⊥

canonicalStrictActuationExpansion : StrictActuationExpansion
canonicalStrictActuationExpansion =
  strictActuationExpansion
    unaidedActionsRemainAIReachable
    generateSubmissionAction
    aiGenerateSubmission
    aiSubmissionWasNotUnaidedReachable

aiMediatedObserver : Observer.Observer FineLegalState CoarseObservation
aiMediatedObserver = layObserver

aiDoesNotDefinitionallyRefineLayObserver : aiMediatedObserver ≡ layObserver
aiDoesNotDefinitionallyRefineLayObserver = refl

record ActuationWithoutRefinement : Set where
  constructor actuationWithoutRefinement
  field
    actuationStrictlyExpands : StrictActuationExpansion
    observerSurfaceUnchanged : aiMediatedObserver ≡ layObserver
    observerStillDecisionUnsafe : DecisionSafe aiMediatedObserver → ⊥

canonicalActuationWithoutRefinement : ActuationWithoutRefinement
canonicalActuationWithoutRefinement =
  actuationWithoutRefinement
    canonicalStrictActuationExpansion
    refl
    layObserverIsNotDecisionSafe

------------------------------------------------------------------------
-- 4. Pareto-live saving branches.  Reuse ParetoPlanning's objective-vector
--    dominance algebra rather than defining a second Pareto order.
------------------------------------------------------------------------

fatalEvidence : Pareto.ObjectiveScore
fatalEvidence = Pareto.mkObjectiveScore "evidence-fit" Pareto.maximise 2 "score" "subjective"

fatalActionability : Pareto.ObjectiveScore
fatalActionability = Pareto.mkObjectiveScore "actionability" Pareto.maximise 1 "score" "subjective"

savingEvidence : Pareto.ObjectiveScore
savingEvidence = Pareto.mkObjectiveScore "evidence-fit" Pareto.maximise 1 "score" "subjective"

savingActionabilityBeforeAI : Pareto.ObjectiveScore
savingActionabilityBeforeAI =
  Pareto.mkObjectiveScore "actionability" Pareto.maximise 0 "score" "subjective"

savingActionabilityAfterAI : Pareto.ObjectiveScore
savingActionabilityAfterAI =
  Pareto.mkObjectiveScore "actionability" Pareto.maximise 2 "score" "AI-expanded"

fatalScores : List Pareto.ObjectiveScore
fatalScores = fatalEvidence ∷ fatalActionability ∷ []

savingScoresBeforeAI : List Pareto.ObjectiveScore
savingScoresBeforeAI = savingEvidence ∷ savingActionabilityBeforeAI ∷ []

savingScoresAfterAI : List Pareto.ObjectiveScore
savingScoresAfterAI = savingEvidence ∷ savingActionabilityAfterAI ∷ []

VectorDominates : List Pareto.ObjectiveScore → List Pareto.ObjectiveScore → Set
VectorDominates better worse =
  Pareto.VectorNoWorse better worse × Pareto.SomeStrictlyBetter better worse

fatalDominatesSavingBeforeAI : VectorDominates fatalScores savingScoresBeforeAI
fatalDominatesSavingBeforeAI =
  Pareto.vector-cons refl (s≤s z≤n)
    (Pareto.vector-cons refl z≤n Pareto.vector-empty)
  , Pareto.strict-head refl (s≤s (s≤s z≤n))

fatalDoesNotDominateSavingAfterAI :
  VectorDominates fatalScores savingScoresAfterAI → ⊥
fatalDoesNotDominateSavingAfterAI domination with proj₁ domination
... | Pareto.vector-cons evidenceNoWorse
      (s≤s z≤n)
      (Pareto.vector-cons actionNoWorse () Pareto.vector-empty)

savingDoesNotDominateFatalAfterAI :
  VectorDominates savingScoresAfterAI fatalScores → ⊥
savingDoesNotDominateFatalAfterAI domination with proj₁ domination
... | Pareto.vector-cons evidenceNoWorse () tail

record PairwiseParetoLiveAfterAI : Set where
  constructor pairwiseParetoLiveAfterAI
  field
    fatalCannotDominateSaving : VectorDominates fatalScores savingScoresAfterAI → ⊥
    savingCannotDominateFatal : VectorDominates savingScoresAfterAI fatalScores → ⊥

savingBranchBecomesPairwiseParetoLiveAfterAI : PairwiseParetoLiveAfterAI
savingBranchBecomesPairwiseParetoLiveAfterAI =
  pairwiseParetoLiveAfterAI
    fatalDoesNotDominateSavingAfterAI
    savingDoesNotDominateFatalAfterAI

------------------------------------------------------------------------
-- 5. Institutional notice: delivery and repetition are weaker than refinement.
------------------------------------------------------------------------

data DeliveredNotice : Set where
  deliveredNotice : DeliveredNotice

repeatedWrittenNoticeObserver : Observer.Observer FineLegalState CoarseObservation
repeatedWrittenNoticeObserver = layObserver

repetitionOfSameNoticeDoesNotRefineDecisionFibre :
  DecisionSafe repeatedWrittenNoticeObserver → ⊥
repetitionOfSameNoticeDoesNotRefineDecisionFibre = layObserverIsNotDecisionSafe

record AccessibleClosureMechanism : Set where
  constructor accessibleClosureMechanism
  field
    ExactDefectIdentified : Set
    exactDefectIdentified : ExactDefectIdentified
    TeachBackAvailable : Set
    teachBackAvailable : TeachBackAvailable
    ConceptualMismatchRepairable : Set
    conceptualMismatchRepairable : ConceptualMismatchRepairable
    SavingPropositionIdentified : Set
    savingPropositionIdentified : SavingPropositionIdentified
    DefinedResearchPeriod : Set
    definedResearchPeriod : DefinedResearchPeriod
    FocusedReplyAvailable : Set
    focusedReplyAvailable : FocusedReplyAvailable
    AdverseBoundaryAfterClosure : Set
    adverseBoundaryAfterClosure : AdverseBoundaryAfterClosure

canonicalAccessibleClosure : AccessibleClosureMechanism
canonicalAccessibleClosure =
  accessibleClosureMechanism
    ⊤ tt
    ⊤ tt
    ⊤ tt
    ⊤ tt
    ⊤ tt
    ⊤ tt
    ⊤ tt

record EffectiveNotice
    {Observation : Set}
    (afterObserver : Observer.Observer FineLegalState Observation) : Set₁ where
  constructor effectiveNotice
  field
    decisionRelevantRefinement : DecisionSafe afterObserver
    accessibleClosure : AccessibleClosureMechanism

open EffectiveNotice public

deliveryAloneDoesNotMakeLayObserverEffective :
  DeliveredNotice → EffectiveNotice layObserver → ⊥
deliveryAloneDoesNotMakeLayObserverEffective delivered notice =
  layObserverIsNotDecisionSafe (decisionRelevantRefinement notice)

diagnosticInteractionIsNotYetEffectiveNotice :
  EffectiveNotice diagnosticObserver → ⊥
diagnosticInteractionIsNotYetEffectiveNotice notice =
  diagnosticObserverIsNotDecisionSafe (decisionRelevantRefinement notice)

expertRefinementWithClosureIsEffectiveNotice : EffectiveNotice expertObserver
expertRefinementWithClosureIsEffectiveNotice =
  effectiveNotice expertObserverIsDecisionSafe canonicalAccessibleClosure

------------------------------------------------------------------------
-- 6. Reasonableness is observer attribution, not proof that the subject owns
--    the reference observer.
------------------------------------------------------------------------

record ReasonablenessObserverGap : Set where
  constructor reasonablenessObserverGap
  field
    referenceObserver : Observer.Observer FineLegalState FineObservation
    referenceObserverSafe : DecisionSafe referenceObserver
    actualObserver : Observer.Observer FineLegalState CoarseObservation
    actualObserverUnsafe : DecisionSafe actualObserver → ⊥

canonicalReasonablenessObserverGap : ReasonablenessObserverGap
canonicalReasonablenessObserverGap =
  reasonablenessObserverGap
    expertObserver
    expertObserverIsDecisionSafe
    layObserver
    layObserverIsNotDecisionSafe

------------------------------------------------------------------------
-- 7. Confusion versus defiance, and the culpability boundary.
------------------------------------------------------------------------

record DecisionConflictInFibre
    {Observation : Set}
    (observe : Observer.Observer FineLegalState Observation) : Set where
  constructor decisionConflictInFibre
  field
    leftState rightState : FineLegalState
    sameSurface : observe leftState ≡ observe rightState
    differentDecision : decision leftState ≡ decision rightState → ⊥

layDecisionConflict : DecisionConflictInFibre layObserver
layDecisionConflict =
  decisionConflictInFibre
    fatalThresholdState
    viableSavingBranchState
    refl
    (λ ())

diagnosticDecisionConflict : DecisionConflictInFibre diagnosticObserver
diagnosticDecisionConflict =
  decisionConflictInFibre
    fatalThresholdState
    viableSavingBranchState
    refl
    (λ ())

record CostsCulpable
    {Observation : Set}
    (observe : Observer.Observer FineLegalState Observation) : Set₁ where
  constructor costsCulpable
  field
    effectiveNoticeBeforePersistence : EffectiveNotice observe
    ContinuedAfterClosure : Set
    continuedAfterClosure : ContinuedAfterClosure

open CostsCulpable public

layPersistenceCannotBePromotedToThisCulpabilityBoundary :
  CostsCulpable layObserver → ⊥
layPersistenceCannotBePromotedToThisCulpabilityBoundary culpable =
  layObserverIsNotDecisionSafe
    (decisionRelevantRefinement (effectiveNoticeBeforePersistence culpable))

diagnosticPersistenceCannotBePromotedToThisCulpabilityBoundary :
  CostsCulpable diagnosticObserver → ⊥
diagnosticPersistenceCannotBePromotedToThisCulpabilityBoundary culpable =
  diagnosticObserverIsNotDecisionSafe
    (decisionRelevantRefinement (effectiveNoticeBeforePersistence culpable))

record ClosedFibreDefianceWitness : Set₁ where
  constructor closedFibreDefianceWitness
  field
    notice : EffectiveNotice expertObserver
    persistedAnyway : LegalDecision
    persistedAnywayIsPersist : persistedAnyway ≡ persistDecision

canonicalClosedFibreDefianceWitness : ClosedFibreDefianceWitness
canonicalClosedFibreDefianceWitness =
  closedFibreDefianceWitness
    expertRefinementWithClosureIsEffectiveNotice
    persistDecision
    refl

------------------------------------------------------------------------
-- 8. Formal equality does not establish effective capability equality.
------------------------------------------------------------------------

data Party : Set where
  individualParty institutionalParty : Party

data FormalRight : Set where
  selfRepresentRight seekCostsRight obtainAdviceRight : FormalRight

data HasFineRefinementAccess : Party → Set where
  institutionalFineAccess : HasFineRefinementAccess institutionalParty

sameFormalRights : Party → List FormalRight
sameFormalRights _ = selfRepresentRight ∷ seekCostsRight ∷ obtainAdviceRight ∷ []

formalRightsEqual : sameFormalRights individualParty ≡ sameFormalRights institutionalParty
formalRightsEqual = refl

individualDoesNotAcquireInstitutionalFineAccess :
  HasFineRefinementAccess individualParty → ⊥
individualDoesNotAcquireInstitutionalFineAccess ()

record FormalEqualityCapabilityGap : Set where
  constructor formalEqualityCapabilityGap
  field
    rightsSurfaceEqual :
      sameFormalRights individualParty ≡ sameFormalRights institutionalParty
    institutionalAccess : HasFineRefinementAccess institutionalParty
    individualAccessImpossible : HasFineRefinementAccess individualParty → ⊥

canonicalFormalEqualityCapabilityGap : FormalEqualityCapabilityGap
canonicalFormalEqualityCapabilityGap =
  formalEqualityCapabilityGap
    refl
    institutionalFineAccess
    individualDoesNotAcquireInstitutionalFineAccess

------------------------------------------------------------------------
-- 9. Same monetary sanction can have different downstream harm.
------------------------------------------------------------------------

data HarmLevel : Set where
  lowMaterialImpact severeMaterialImpact : HarmLevel

sanctionAmount : Party → Nat
sanctionAmount _ = 3

sanctionHarm : Party → HarmLevel
sanctionHarm individualParty = severeMaterialImpact
sanctionHarm institutionalParty = lowMaterialImpact

sameNominalSanction : sanctionAmount individualParty ≡ sanctionAmount institutionalParty
sameNominalSanction = refl

sameNominalSanctionDoesNotForceSameHarm :
  sanctionHarm individualParty ≡ sanctionHarm institutionalParty → ⊥
sameNominalSanctionDoesNotForceSameHarm ()

------------------------------------------------------------------------
-- 10. Chilling / future-help contraction reuses OptionConeCoercionExact.
------------------------------------------------------------------------

sanctionLikeTransitionMayContractFutureHelpSeeking :
  OptionCone.StrictSafeReachabilityContraction
    OptionCone.demoReachability
    OptionCone.beforeResponse
    OptionCone.coerciveOutcome
sanctionLikeTransitionMayContractFutureHelpSeeking =
  OptionCone.canonicalCoerciveReachabilityContraction

futureHelpSeekingIsExplicitlyLostInCanonicalContraction :
  OptionCone.DemoAvailable OptionCone.coerciveOutcome OptionCone.futureHelpSeeking → ⊥
futureHelpSeekingIsExplicitlyLostInCanonicalContraction =
  OptionCone.StrictSafeReachabilityContraction.lostAfterImpossible
    OptionCone.canonicalCoerciveReachabilityContraction

------------------------------------------------------------------------
-- 11. Compact boundary.
------------------------------------------------------------------------

record InstitutionalNoticeActuationCulpabilityBoundary : Set where
  constructor institutionalNoticeActuationCulpabilityBoundary
  field
    wrongModelExhaustsLayProblem : Bool
    repeatedDeliveryImpliesRefinement : Bool
    diagnosticInteractionImpliesClosure : Bool
    aiActuationImpliesObserverRefinement : Bool
    referenceObserverEqualsActualObserver : Bool
    formalContestabilityImpliesAffordability : Bool
    equalFormalRightsImplyEqualCapability : Bool
    equalNominalCostImpliesEqualHarm : Bool
    persistenceInsideDecisionConflictImpliesDefiance : Bool
    culpabilityRequiresDecisionSafeRefinement : Bool
    culpabilityRequiresAccessibleClosure : Bool
    aiCanMoveSavingBranchOntoPairwiseParetoFrontier : Bool

canonicalInstitutionalNoticeActuationCulpabilityBoundary :
  InstitutionalNoticeActuationCulpabilityBoundary
canonicalInstitutionalNoticeActuationCulpabilityBoundary =
  institutionalNoticeActuationCulpabilityBoundary
    false false false false false false false false false true true true

institutionalNoticeActuationCulpabilityStatement : String
institutionalNoticeActuationCulpabilityStatement =
  "A subject may occupy a decision-conflicted live fibre rather than merely hold a wrong proposition. Repeated notice and diagnostic interaction need not close that fibre; AI can strictly expand institutional actuation while leaving the observer unchanged and can restore a saving branch to a pairwise Pareto frontier. Exceptional culpability is therefore represented only after decision-safe refinement plus accessible closure, while formal rights, refinement access, sanction recovery and downstream harm remain separately typed capability questions."
