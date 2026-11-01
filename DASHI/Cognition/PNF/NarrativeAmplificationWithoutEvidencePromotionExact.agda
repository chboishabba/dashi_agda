module DASHI.Cognition.PNF.NarrativeAmplificationWithoutEvidencePromotionExact where

------------------------------------------------------------------------
-- AUDIENCE AMPLIFICATION WITHOUT EVIDENCE PROMOTION
--
-- Cross-pollination theorem joining provenance lineage, four consumer planes,
-- and cultural replication.  Repetition may increase salience and move a
-- cultural/rhetorical state while preserving both the factual coordinate and
-- the independent evidence origin.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as N
import DASHI.Cognition.PNF.ConsumerIndexedNarrativeProjectionExact as C

record AmplifiedNarrative : Set where
  constructor amplifiedNarrative
  field
    signal : N.NarrativeSignal
    planes : N.FourPlaneState
      C.FactStatus C.RhetoricalStatus C.CulturalStatus C.InstitutionalStatus

open AmplifiedNarrative public

baseNarrative : AmplifiedNarrative
baseNarrative =
  amplifiedNarrative
    (N.narrativeSignal (N.evidenceLineage 7 0) 0)
    (N.fourPlaneState
      C.factUnresolved
      C.lowImpact
      C.localArtifact
      C.noDisposition)

amplifyNarrative : AmplifiedNarrative → AmplifiedNarrative
amplifyNarrative (amplifiedNarrative sig state) =
  amplifiedNarrative
    (N.replicateSignal sig)
    (N.updateCultural C.replicatedAnthem
      (N.updateRhetorical C.highImpact state))

amplificationPreservesEvidenceOrigin :
  N.originId (N.lineage (signal (amplifyNarrative baseNarrative)))
  ≡ N.originId (N.lineage (signal baseNarrative))
amplificationPreservesEvidenceOrigin = refl

amplificationRaisesSalience :
  N.salience (signal (amplifyNarrative baseNarrative)) ≡ 1
amplificationRaisesSalience = refl

amplificationPreservesFact :
  N.factualState (planes (amplifyNarrative baseNarrative))
  ≡ N.factualState (planes baseNarrative)
amplificationPreservesFact = refl

amplificationChangesCulturalState :
  N.culturalState (planes (amplifyNarrative baseNarrative))
  ≡ N.culturalState (planes baseNarrative) → ⊥
amplificationChangesCulturalState ()

amplificationChangesRhetoricalState :
  N.rhetoricalState (planes (amplifyNarrative baseNarrative))
  ≡ N.rhetoricalState (planes baseNarrative) → ⊥
amplificationChangesRhetoricalState ()

------------------------------------------------------------------------
-- The core result: increased public replication is compatible with unchanged
-- factual state and unchanged evidence origin.  Therefore replication count
-- and cultural dominance cannot be used as substitutes for corroboration.
------------------------------------------------------------------------

record AmplificationSeparationWitness : Set where
  constructor amplificationSeparationWitness
  field
    sameOrigin :
      N.originId (N.lineage (signal (amplifyNarrative baseNarrative)))
      ≡ N.originId (N.lineage (signal baseNarrative))
    sameFact :
      N.factualState (planes (amplifyNarrative baseNarrative))
      ≡ N.factualState (planes baseNarrative)
    culturalMoved :
      N.culturalState (planes (amplifyNarrative baseNarrative))
      ≡ N.culturalState (planes baseNarrative) → ⊥

canonicalAmplificationSeparation : AmplificationSeparationWitness
canonicalAmplificationSeparation =
  amplificationSeparationWitness
    amplificationPreservesEvidenceOrigin
    amplificationPreservesFact
    amplificationChangesCulturalState
