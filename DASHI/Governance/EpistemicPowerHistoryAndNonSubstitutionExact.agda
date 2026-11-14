module DASHI.Governance.EpistemicPowerHistoryAndNonSubstitutionExact where

-- Constructive, finite DASHI models motivated by Satta (2024) and
-- Tuck/Yang (2012). No claims that these models are complete readings,
-- psychological diagnoses, or proofs about particular institutions.
-- This module deliberately imports existing Golden nonfactorability
-- machinery rather than re-proving its generic transport theorem.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Governance.EpistemicPowerStructuralRetentionExact as Retention

------------------------------------------------------------------------
-- H0: Three distinct epistemic tasks. These are workload coordinates,
-- not clinical or phenomenological measurements of cognitive fatigue.
------------------------------------------------------------------------

data EpistemicTask : Set where
  determineBelief retainBelief communicateBelief : EpistemicTask

record TaskBurden : Set where
  constructor task-burden
  field
    determining : Nat
    retaining : Nat
    communicating : Nat

open TaskBurden public

emptyBurden : TaskBurden
emptyBurden = task-burden 0 0 0

incrementTask : EpistemicTask → TaskBurden → TaskBurden
incrementTask determineBelief (task-burden d r c) =
  task-burden (suc d) r c
incrementTask retainBelief (task-burden d r c) =
  task-burden d (suc r) c
incrementTask communicateBelief (task-burden d r c) =
  task-burden d r (suc c)

foldTaskHistory : List EpistemicTask → TaskBurden
foldTaskHistory [] = emptyBurden
foldTaskHistory (task ∷ tasks) = incrementTask task (foldTaskHistory tasks)

singleAcceptedHistory : List EpistemicTask
singleAcceptedHistory = []

reopenedAndRecommunicatedHistory : List EpistemicTask
reopenedAndRecommunicatedHistory =
  retainBelief ∷ communicateBelief ∷ []

repeatedHistoryHasRetentionDemand :
  retaining (foldTaskHistory reopenedAndRecommunicatedHistory)
  ≡ suc 0
repeatedHistoryHasRetentionDemand = refl

repeatedHistoryHasCommunicationDemand :
  communicating (foldTaskHistory reopenedAndRecommunicatedHistory)
  ≡ suc 0
repeatedHistoryHasCommunicationDemand = refl

repeatedHistoryHasNoDeterminationDemand :
  determining (foldTaskHistory reopenedAndRecommunicatedHistory)
  ≡ 0
repeatedHistoryHasNoDeterminationDemand = refl

------------------------------------------------------------------------
-- H1: Public outcome is a projection that discards review-workload history.
------------------------------------------------------------------------

data PublicDisposition : Set where
  conclusionAccepted : PublicDisposition

visibleDisposition : List EpistemicTask → PublicDisposition
visibleDisposition _ = conclusionAccepted

retentionDemand : List EpistemicTask → Nat
retentionDemand tasks = retaining (foldTaskHistory tasks)

communicationDemand : List EpistemicTask → Nat
communicationDemand tasks = communicating (foldTaskHistory tasks)

sameOutcomeDifferentRetentionHistory :
  Intersection.NonFactorabilityWitness
    visibleDisposition retentionDemand
sameOutcomeDifferentRetentionHistory =
  Intersection.nonFactorabilityWitness
    singleAcceptedHistory
    reopenedAndRecommunicatedHistory
    refl
    (λ ())

sameOutcomeDifferentCommunicationHistory :
  Intersection.NonFactorabilityWitness
    visibleDisposition communicationDemand
sameOutcomeDifferentCommunicationHistory =
  Intersection.nonFactorabilityWitness
    singleAcceptedHistory
    reopenedAndRecommunicatedHistory
    refl
    (λ ())

anyPublicRechartStillLosesRetentionBurden :
  ∀ {Recharted : Set} →
  (rechart : PublicDisposition → Recharted) →
  Intersection.FactorsThrough
    (λ history → rechart (visibleDisposition history))
    retentionDemand → ⊥
anyPublicRechartStillLosesRetentionBurden rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart sameOutcomeDifferentRetentionHistory

anyPublicRechartStillLosesCommunicationBurden :
  ∀ {Recharted : Set} →
  (rechart : PublicDisposition → Recharted) →
  Intersection.FactorsThrough
    (λ history → rechart (visibleDisposition history))
    communicationDemand → ⊥
anyPublicRechartStillLosesCommunicationBurden rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart sameOutcomeDifferentCommunicationHistory

------------------------------------------------------------------------
-- H2: A burden observation does not establish intentional manipulation.
-- Equal externally reported workloads may arise under rival motivations.
------------------------------------------------------------------------

data ReviewPurpose : Set where
  legitimateQualityReview strategicProceduralObstruction : ReviewPurpose

record ReviewEpisode : Set where
  constructor episode
  field
    recordedTasks : List EpistemicTask
    purpose : ReviewPurpose

open ReviewEpisode public

legitimateEpisode : ReviewEpisode
legitimateEpisode =
  episode reopenedAndRecommunicatedHistory legitimateQualityReview

obstructiveEpisode : ReviewEpisode
obstructiveEpisode =
  episode reopenedAndRecommunicatedHistory strategicProceduralObstruction

observedTasks : ReviewEpisode → List EpistemicTask
observedTasks = recordedTasks

statedPurpose : ReviewEpisode → ReviewPurpose
statedPurpose = purpose

sameTasksCannotIdentifyPurpose :
  Intersection.NonFactorabilityWitness observedTasks statedPurpose
sameTasksCannotIdentifyPurpose =
  Intersection.nonFactorabilityWitness
    legitimateEpisode obstructiveEpisode refl (λ ())

taskRechartCannotInferIntent :
  ∀ {Recharted : Set} →
  (rechart : List EpistemicTask → Recharted) →
  Intersection.FactorsThrough
    (λ ep → rechart (observedTasks ep))
    statedPurpose → ⊥
taskRechartCannotInferIntent rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart sameTasksCannotIdentifyPurpose

------------------------------------------------------------------------
-- D0: Inclusion, land, and sovereignty are separate observables.
-- The four worlds are *logical possibility witnesses*, not a ranking of
-- decolonial outcomes or a claim that Booleans capture sovereignty.
------------------------------------------------------------------------

data CommitmentsState : Set where
  neitherCommitment landOnly sovereigntyOnly bothCommitments : CommitmentsState

data InstitutionalInclusionObservation : Set where
  sameInclusionStatement : InstitutionalInclusionObservation

inclusionReport : CommitmentsState → InstitutionalInclusionObservation
inclusionReport _ = sameInclusionStatement

landCommitment : CommitmentsState → Bool
landCommitment neitherCommitment = false
landCommitment landOnly = true
landCommitment sovereigntyOnly = false
landCommitment bothCommitments = true

sovereigntyCommitment : CommitmentsState → Bool
sovereigntyCommitment neitherCommitment = false
sovereigntyCommitment landOnly = false
sovereigntyCommitment sovereigntyOnly = true
sovereigntyCommitment bothCommitments = true

landDoesNotEntailSovereignty :
  ((s : CommitmentsState) →
    landCommitment s ≡ true →
    sovereigntyCommitment s ≡ true) → ⊥
landDoesNotEntailSovereignty entails =
  falseCannotEqualTrue (entails landOnly refl)
  where
    falseCannotEqualTrue : false ≡ true → ⊥
    falseCannotEqualTrue ()

sovereigntyDoesNotEntailLand :
  ((s : CommitmentsState) →
    sovereigntyCommitment s ≡ true →
    landCommitment s ≡ true) → ⊥
sovereigntyDoesNotEntailLand entails =
  falseCannotEqualTrue (entails sovereigntyOnly refl)
  where
    falseCannotEqualTrue : false ≡ true → ⊥
    falseCannotEqualTrue ()

inclusionCannotDetermineLand :
  Intersection.NonFactorabilityWitness inclusionReport landCommitment
inclusionCannotDetermineLand =
  Intersection.nonFactorabilityWitness
    neitherCommitment landOnly refl (λ ())

inclusionCannotDetermineSovereignty :
  Intersection.NonFactorabilityWitness
    inclusionReport sovereigntyCommitment
inclusionCannotDetermineSovereignty =
  Intersection.nonFactorabilityWitness
    neitherCommitment sovereigntyOnly refl (λ ())

inclusionRechartCannotDetermineSovereignty :
  ∀ {Recharted : Set} →
  (rechart : InstitutionalInclusionObservation → Recharted) →
  Intersection.FactorsThrough
    (λ s → rechart (inclusionReport s))
    sovereigntyCommitment → ⊥
inclusionRechartCannotDetermineSovereignty rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart inclusionCannotDetermineSovereignty

------------------------------------------------------------------------
-- D1: The existing finite authority-retention countermodel composes
-- with the generic nonfactorability witness. No source claim promoted.
------------------------------------------------------------------------

combinedParticipationAuthorityObstruction :
  Intersection.FactorsThrough
    Retention.participation Retention.bindingAuthority → ⊥
combinedParticipationAuthorityObstruction =
  Intersection.witnessRulesOutEveryFlatFactorisation
    Retention.institutionalProjectionCannotRecoverAuthority
