module DASHI.Cognition.PNF.ConsumerIndexedNarrativeProjectionExact where

------------------------------------------------------------------------
-- CONSUMER-INDEXED NARRATIVE PROJECTION
--
-- The same cultural artifact can be evaluated by factual, rhetorical,
-- cultural, and institutional consumers without those outputs collapsing into
-- one truth coordinate.  This is the narrative specialization of the repo's
-- consumer-relative quotient discipline.
--
-- Worked legal reference:
--   Graham v. UMG Recordings, Inc., No. 1:25-cv-00399 (S.D.N.Y. 2025),
--   Document 96, dismissed the challenged Not Like Us statements as
--   nonactionable opinion in rap-battle context.  This module deliberately
--   does NOT promote that legal disposition into a truth verdict on the
--   underlying lyrical allegations.
-- No DOI is asserted for the judicial opinion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Independent consumer codomains.
------------------------------------------------------------------------

data FactStatus : Set where
  factSupported factRefuted factUnresolved : FactStatus

data RhetoricalStatus : Set where
  lowImpact highImpact contestedImpact : RhetoricalStatus

data CulturalStatus : Set where
  localArtifact membershipClassifier replicatedAnthem : CulturalStatus

data InstitutionalStatus : Set where
  noDisposition nonActionableOpinion actionableStatement : InstitutionalStatus

record ConsumerProjection (Fine : Set) : Set₁ where
  constructor consumerProjection
  field
    factual : Fine → FactStatus
    rhetorical : Fine → RhetoricalStatus
    cultural : Fine → CulturalStatus
    institutional : Fine → InstitutionalStatus

open ConsumerProjection public

------------------------------------------------------------------------
-- No cross-plane authority is manufactured from the type signatures.
------------------------------------------------------------------------

data InstitutionalSettlesFact : InstitutionalStatus → FactStatus → Set where

nonActionableOpinionDoesNotSettleSupported :
  InstitutionalSettlesFact nonActionableOpinion factSupported → ⊥
nonActionableOpinionDoesNotSettleSupported ()

nonActionableOpinionDoesNotSettleRefuted :
  InstitutionalSettlesFact nonActionableOpinion factRefuted → ⊥
nonActionableOpinionDoesNotSettleRefuted ()

------------------------------------------------------------------------
-- Concrete Not Like Us projection surface.  The factual axis stays unresolved
-- here because this module is not a fact-finding court or evidentiary engine.
------------------------------------------------------------------------

data NarrativeArtifact : Set where
  notLikeUsArtifact : NarrativeArtifact

notLikeUsConsumers : ConsumerProjection NarrativeArtifact
notLikeUsConsumers =
  consumerProjection
    (λ artifact → factUnresolved)
    (λ artifact → highImpact)
    (λ artifact → replicatedAnthem)
    (λ artifact → nonActionableOpinion)

notLikeUsFactRemainsSeparate :
  factual notLikeUsConsumers notLikeUsArtifact ≡ factUnresolved
notLikeUsFactRemainsSeparate = refl

notLikeUsCulturalProjection :
  cultural notLikeUsConsumers notLikeUsArtifact ≡ replicatedAnthem
notLikeUsCulturalProjection = refl

notLikeUsInstitutionalProjection :
  institutional notLikeUsConsumers notLikeUsArtifact ≡ nonActionableOpinion
notLikeUsInstitutionalProjection = refl

------------------------------------------------------------------------
-- Same artifact, different consumer: this is a typed distinction, not a
-- contradiction requiring one plane to overwrite the others.
------------------------------------------------------------------------

record ParallelNarrativeState : Set where
  constructor parallelNarrativeState
  field
    fact : FactStatus
    rhetoric : RhetoricalStatus
    culture : CulturalStatus
    institution : InstitutionalStatus

open ParallelNarrativeState public

notLikeUsParallelState : ParallelNarrativeState
notLikeUsParallelState =
  parallelNarrativeState
    factUnresolved
    highImpact
    replicatedAnthem
    nonActionableOpinion

legalDispositionLeavesFactCoordinateUntouched :
  fact notLikeUsParallelState ≡ factUnresolved
legalDispositionLeavesFactCoordinateUntouched = refl
