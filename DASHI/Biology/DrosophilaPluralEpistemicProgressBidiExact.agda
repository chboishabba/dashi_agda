module DASHI.Biology.DrosophilaPluralEpistemicProgressBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Fly
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method

------------------------------------------------------------------------
-- DROSOPHILA SAME-TRIAL EVIDENCE <-> PROVENANCE-QUORUM METHODOLOGY
--
-- Multiple modalities from one animal/trial may corroborate a result without
-- becoming independent replication.  The appropriate progress route is to
-- close provenance independence (for example across trials/animals/datasets),
-- not merely accumulate more descendants of the same root.
------------------------------------------------------------------------

sameTrialAssessment : Fly.EvidenceDependenceAssessment
sameTrialAssessment = record
  { relation = Fly.sameTrialCorroboration
  ; sharedAnimalRoot = true
  ; sharedTrialRoot = true
  ; sharedRegistrationRoot = true
  ; sharedPreprocessingRoot = true
  ; independentReplicationClaim = false
  ; sameTrialBlocksIndependentReplication = λ _ → refl
  ; sameAnimalBlocksCrossAnimalReplication = λ _ ()
  }

sameTrialEvidenceDoesNotClaimIndependentReplication :
  Fly.independentReplicationClaim sameTrialAssessment ≡ false
sameTrialEvidenceDoesNotClaimIndependentReplication = refl

sameTrialRelationRetained :
  Fly.relation sameTrialAssessment ≡ Fly.sameTrialCorroboration
sameTrialRelationRetained = refl

nextMethodologicalRoute : Method.EpistemicProgressRoute
nextMethodologicalRoute = Method.establishIndependentProvenance

data ModalityMultiplicityCreatesReplication : Set where
data SameRegistrationCreatesIndependentEvidence : Set where

modalityMultiplicityDoesNotCreateReplication :
  ModalityMultiplicityCreatesReplication → ⊥
modalityMultiplicityDoesNotCreateReplication ()

sameRegistrationDoesNotCreateIndependentEvidence :
  SameRegistrationCreatesIndependentEvidence → ⊥
sameRegistrationDoesNotCreateIndependentEvidence ()

record DrosophilaPluralEpistemicBoundary : Set where
  constructor drosophila-plural-epistemic-boundary
  field
    sameTrialMayCorroborate : Bool
    sameTrialCountsAsIndependentReplication : Bool
    sharedRegistrationCountsAsIndependentReplication : Bool
    independentProgressMayRequireNewProvenanceRoot : Bool
    provenanceClosureProvesBiologicalMechanism : Bool

canonicalDrosophilaPluralEpistemicBoundary : DrosophilaPluralEpistemicBoundary
canonicalDrosophilaPluralEpistemicBoundary =
  drosophila-plural-epistemic-boundary true false false true false
