module DASHI.Governance.AutonomyReopeningCriterion where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DevelopmentalAgencyState as Agency
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Developmental reopening.
--
-- A one-step reduction in option space is not sufficient for an
-- indoctrination conclusion.  Protective rules, scaffolding and ordinary
-- education can temporarily constrain choice while later increasing the
-- learner's access to reasons, alternatives and independent verification.
-- The candidate concern is persistent suppression relative to a stated
-- autonomy-preserving counterfactual baseline.
------------------------------------------------------------------------

record ReopeningSystem : Set₁ where
  field
    Subject : Set
    Domain : Set
    Time : Set
    Capacity : Set

    actualRevisionCapacity : Subject → Domain → Time → Capacity
    availableRevisionCapacity : Subject → Domain → Time → Capacity
    Below : Capacity → Capacity → Set
    MatureAfter : Time → Set

open ReopeningSystem public

record RevisionDeficit
  (S : ReopeningSystem)
  (subject : Subject S)
  (domain : Domain S)
  (time : Time S)
  : Set₁ where
  field
    actualBelowAvailable :
      Below S
        (actualRevisionCapacity S subject domain time)
        (availableRevisionCapacity S subject domain time)

record PersistentRevisionSuppression
  (S : ReopeningSystem)
  (subject : Subject S)
  (domain : Domain S)
  : Set₁ where
  field
    thresholdTime : Time S
    afterThreshold : Time S → Set
    deficitPersists :
      (time : Time S) →
      afterThreshold time →
      RevisionDeficit S subject domain time
    thresholdIsDevelopmentallyRelevant : MatureAfter S thresholdTime

record DevelopmentalReopening
  (S : ReopeningSystem)
  (subject : Subject S)
  (domain : Domain S)
  : Set₁ where
  field
    reopeningTime : Time S
    actualMeetsAvailable :
      ¬ Below S
        (actualRevisionCapacity S subject domain reopeningTime)
        (availableRevisionCapacity S subject domain reopeningTime)

------------------------------------------------------------------------
-- Candidate indoctrination is a bounded formal classification, not a truth,
-- diagnosis, abuse, fraud or legal conclusion.
------------------------------------------------------------------------

record CandidateIndoctrination
  (S : ReopeningSystem)
  (subject : Subject S)
  (domain : Domain S)
  : Set₁ where
  field
    persistentSuppression : PersistentRevisionSuppression S subject domain
    reasonsOrAlternativesSystematicallyRestricted : Set
    independentVerificationSystematicallyRestricted : Set


data CandidateIndoctrinationEstablishesClinicalHarm : Set where

data CandidateIndoctrinationEstablishesLegalWrong : Set where

data CandidateIndoctrinationEstablishesBeliefFalsehood : Set where

candidateIndoctrinationDoesNotEstablishClinicalHarm :
  CandidateIndoctrinationEstablishesClinicalHarm → ⊥
candidateIndoctrinationDoesNotEstablishClinicalHarm ()

candidateIndoctrinationDoesNotEstablishLegalWrong :
  CandidateIndoctrinationEstablishesLegalWrong → ⊥
candidateIndoctrinationDoesNotEstablishLegalWrong ()

candidateIndoctrinationDoesNotEstablishBeliefFalsehood :
  CandidateIndoctrinationEstablishesBeliefFalsehood → ⊥
candidateIndoctrinationDoesNotEstablishBeliefFalsehood ()

------------------------------------------------------------------------
-- Reflexivity: an anti-indoctrination theory must itself permit revision.
------------------------------------------------------------------------

record ReflexiveRevisionWitness : Set₁ where
  field
    Claim : Set
    Evidence : Set
    revise : Claim → Evidence → Claim
    claim : Claim
    disconfirmingEvidence : Evidence
    revisionPossible : ¬ (revise claim disconfirmingEvidence ≡ claim)

record AutonomyReopeningBoundary : Set where
  constructor autonomyReopeningBoundary
  field
    asymmetryAloneIsIndoctrination : Bool
    temporaryScaffoldingAloneIsIndoctrination : Bool
    persistentSuppressionIsCandidateCriterion : Bool
    candidateCriterionCreatesClinicalConclusion : Bool
    candidateCriterionCreatesLegalConclusion : Bool
    candidateCriterionCreatesTruthConclusion : Bool
    theoryMustPermitSelfRevision : Bool

canonicalAutonomyReopeningBoundary : AutonomyReopeningBoundary
canonicalAutonomyReopeningBoundary =
  autonomyReopeningBoundary false false true false false false true

record AutonomyReopeningReceipt : Set where
  constructor autonomyReopeningReceipt
  field
    label : String
    developmentalAgencyReceipt : Agency.DevelopmentalAgencyReceipt
    sourceAtlas : List Sources.ScholarlySource
    boundary : AutonomyReopeningBoundary

canonicalAutonomyReopeningReceipt : AutonomyReopeningReceipt
canonicalAutonomyReopeningReceipt =
  autonomyReopeningReceipt
    "developmental reopening rather than one-step preference suppression"
    Agency.canonicalDevelopmentalAgencyReceipt
    (Sources.indoctrinationSpaceReasons ∷ Sources.epistemicTrustReview ∷ [])
    canonicalAutonomyReopeningBoundary
