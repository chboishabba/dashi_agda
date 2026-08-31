module DASHI.Governance.MaathaiSituatedProvisioningAuthorityExact where

open import DASHI.Core.Prelude
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- MAATHAI: SITUATED NEED EVIDENCE -> ACTION -> ORGANISATION -> AUTHORITY
--
-- Wangari Maathai, Nobel Lecture, Nobel Peace Prize 2004.
-- Stable institutional source: NobelPrize.org Wangari Maathai Nobel Lecture.
--
-- Maathai describes the Green Belt Movement as responding to needs identified
-- by rural women, with ecological action later expanding into questions of good
-- governance and democratic organisation.  The finite path below is a bounded
-- positive formal interpretation, not a controlled causal evaluation.
------------------------------------------------------------------------

data SituatedNeedEvidence : Set where ruralWomenIdentifiedNeeds : SituatedNeedEvidence
data EcologicalAction : Set where treePlantingAction : EcologicalAction
data CollectiveOrganisation : Set where greenBeltOrganisation : CollectiveOrganisation
data PoliticalAuthority : Set where democraticMovementAuthority : PoliticalAuthority

record SituatedProvisioningAuthorityPath : Set where
  constructor situatedProvisioningAuthorityPath
  field
    needEvidence : SituatedNeedEvidence
    ecologicalAction : EcologicalAction
    collectiveOrganisation : CollectiveOrganisation
    politicalAuthority : PoliticalAuthority

open SituatedProvisioningAuthorityPath public

canonicalMaathaiPath : SituatedProvisioningAuthorityPath
canonicalMaathaiPath =
  situatedProvisioningAuthorityPath
    ruralWomenIdentifiedNeeds
    treePlantingAction
    greenBeltOrganisation
    democraticMovementAuthority

-- The stages remain separately typed.  Ecological functioning/action does not
-- definitionally manufacture organisation or political authority.
record MaathaiStageBoundary : Set where
  constructor maathaiStageBoundary
  field
    situatedNeedEvidenceRequiresExternalExpertObserver : Bool
    situatedNeedEvidenceRequiresExternalExpertObserverIsFalse :
      situatedNeedEvidenceRequiresExternalExpertObserver ≡ false
    ecologicalActionEqualsCollectiveOrganisation : Bool
    ecologicalActionEqualsCollectiveOrganisationIsFalse :
      ecologicalActionEqualsCollectiveOrganisation ≡ false
    ecologicalActionEqualsPoliticalAuthority : Bool
    ecologicalActionEqualsPoliticalAuthorityIsFalse :
      ecologicalActionEqualsPoliticalAuthority ≡ false
    collectiveOrganisationEqualsPoliticalAuthority : Bool
    collectiveOrganisationEqualsPoliticalAuthorityIsFalse :
      collectiveOrganisationEqualsPoliticalAuthority ≡ false
    sourceIsControlledCausalEvaluation : Bool
    sourceIsControlledCausalEvaluationIsFalse : sourceIsControlledCausalEvaluation ≡ false

canonicalMaathaiStageBoundary : MaathaiStageBoundary
canonicalMaathaiStageBoundary =
  maathaiStageBoundary false refl false refl false refl false refl false refl

source : Sources.SourceReference
source = Sources.maathai2004
