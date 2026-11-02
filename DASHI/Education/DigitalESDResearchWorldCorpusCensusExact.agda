module DASHI.Education.DigitalESDResearchWorldCorpusCensusExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDWorldSourceCoverageCensusExact as Registry
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDStudyClaimPilotExact as Pilot
import DASHI.Education.DigitalESDStudyClaimPilotExtensionExact as Extended
import DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact as Quantitative
import DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionExact as Uncertainty
import DASHI.Education.DigitalESDInstitutionalEvaluationPilotExact as Institutional
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact as Randomized
import DASHI.Education.DigitalESDColladoLongitudinalClaimExact as Longitudinal
import DASHI.Education.DigitalESDStudyResultPNFProofSearchExact as Result
import DASHI.Education.DigitalESDStudyEvidencePNFExtensionExact as Evidence
import DASHI.Education.DigitalESDStudyProcessingCensusExact as Processing

------------------------------------------------------------------------
-- K01b: registry entries and independently existing study-profile OCCURRENCES.
-- Not a deduplicated source universe; a source may have several analysis
-- profiles, and a future exact source-identity equivalence must reconcile them.
-- No DOI, title, claim, outcome, passage or review status is fabricated.
------------------------------------------------------------------------

pilotStudyProfiles : List Ceiling.StudyClaimProfile
pilotStudyProfiles =
  Pilot.pilotProfiles
  Registry.++ Extended.extensionProfiles
  Registry.++ (Quantitative.brasslerPilotProfile
             ∷ Uncertainty.iaqPilotProfile
             ∷ Institutional.uneceFifthEvaluationPilotProfile
             ∷ Randomized.greenMolloyDugganPilotProfile
             ∷ Longitudinal.colladoLongitudinalProfile
             ∷ [])

pilotProfileOccurrenceCount : Registry.length pilotStudyProfiles ≡ 14
pilotProfileOccurrenceCount = refl

data CorpusOccurrence : Set where
  inheritedRegistry : Registry.WorldSourceCoverageRow → CorpusOccurrence
  existingStudyProfile : Ceiling.StudyClaimProfile → CorpusOccurrence

registeredOccurrences : List CorpusOccurrence
registeredOccurrences =
  Registry.map inheritedRegistry Registry.worldSourceCoverageRows

studyProfileOccurrences : List CorpusOccurrence
studyProfileOccurrences =
  Registry.map existingStudyProfile pilotStudyProfiles

combinedResearchOccurrences : List CorpusOccurrence
combinedResearchOccurrences =
  registeredOccurrences Registry.++ studyProfileOccurrences

registeredOccurrenceCount : Registry.length registeredOccurrences ≡ 25
registeredOccurrenceCount = refl

expandedOccurrenceCount : Registry.length combinedResearchOccurrences ≡ 39
expandedOccurrenceCount = refl

-- The study sources retain their real AttributedSource value instead of a
-- hand-copied URL. Source equality here is definitionally sourced from the
-- actual profile, not guessed from a paper title.
record StudySourceFibre (profile : Ceiling.StudyClaimProfile) : Set where
  constructor study-source-fibre
  field
    exactSource : Attr.AttributedSource
    profileUsesExactSource : Ceiling.source profile ≡ exactSource
    canonicalSourceURL : String
    urlIsFromExactSource : canonicalSourceURL ≡ Attr.canonicalURL exactSource

open StudySourceFibre public

studySourceFibre : (p : Ceiling.StudyClaimProfile) → StudySourceFibre p
studySourceFibre p = study-source-fibre
  (Ceiling.source p) refl
  (Attr.canonicalURL (Ceiling.source p)) refl

studiedFibres : List (Ceiling.StudyClaimProfile)
studiedFibres = pilotStudyProfiles

-- K01c first actually connected claim/PNF surface: preserve the exact PNF
-- audit object and prove the associated study profile is precisely its owner.
-- PNF assertions are candidates; these are NOT reviewed EvidenceSpan objects.
record ResultClaimFibre (audit : Result.StudyResultAudit) : Set where
  constructor result-claim-fibre
  field
    exactProfile : Ceiling.StudyClaimProfile
    profileIsAuditOwner : exactProfile ≡ Result.profile audit
    ownerFibre : StudySourceFibre exactProfile

resultClaimFibre :
  (audit : Result.StudyResultAudit) → ResultClaimFibre audit
resultClaimFibre audit =
  result-claim-fibre (Result.profile audit) refl
    (studySourceFibre (Result.profile audit))

record EvidenceClaimFibre (audit : Evidence.StudyEvidencePNFAudit) : Set where
  constructor evidence-claim-fibre
  field
    exactProfile : Ceiling.StudyClaimProfile
    profileIsAuditOwner : exactProfile ≡ Evidence.profile audit
    ownerFibre : StudySourceFibre exactProfile

evidenceClaimFibre :
  (audit : Evidence.StudyEvidencePNFAudit) → EvidenceClaimFibre audit
evidenceClaimFibre audit =
  evidence-claim-fibre (Evidence.profile audit) refl
    (studySourceFibre (Evidence.profile audit))

resultAuditsWithOriginalOwners :
  List Result.StudyResultAudit
resultAuditsWithOriginalOwners = Result.studyResultAudits

evidenceAuditsWithOriginalOwners :
  List Evidence.StudyEvidencePNFAudit
evidenceAuditsWithOriginalOwners = Evidence.studyEvidencePNFAudits

resultPNFOccurrenceCount :
  Registry.length resultAuditsWithOriginalOwners ≡ 5
resultPNFOccurrenceCount = refl

evidencePNFOccurrenceCount :
  Registry.length evidenceAuditsWithOriginalOwners ≡ 8
evidencePNFOccurrenceCount = refl

-- Each list element is still a typed source owner; map over it to construct
-- the dependent source/profile receipt for that precise audit.
record ResultClaimCensusRow : Set where
  constructor result-claim-census-row
  field
    audit : Result.StudyResultAudit
    sourceLink : ResultClaimFibre audit

record EvidenceClaimCensusRow : Set where
  constructor evidence-claim-census-row
  field
    audit : Evidence.StudyEvidencePNFAudit
    sourceLink : EvidenceClaimFibre audit

asResultRow : Result.StudyResultAudit → ResultClaimCensusRow
asResultRow a = result-claim-census-row a (resultClaimFibre a)

asEvidenceRow : Evidence.StudyEvidencePNFAudit → EvidenceClaimCensusRow
asEvidenceRow a = evidence-claim-census-row a (evidenceClaimFibre a)

resultClaimRows : List ResultClaimCensusRow
resultClaimRows = Registry.map asResultRow resultAuditsWithOriginalOwners

evidenceClaimRows : List EvidenceClaimCensusRow
evidenceClaimRows = Registry.map asEvidenceRow evidenceAuditsWithOriginalOwners

resultClaimRowCount : Registry.length resultClaimRows ≡ 5
resultClaimRowCount = refl

evidenceClaimRowCount : Registry.length evidenceClaimRows ≡ 8
evidenceClaimRowCount = refl

-- Keep the ERIC processing ledger an independent population: 43,996 metadata
-- records are not additional study evidence or 43,996 reconstructed worlds.
metadataUniverseRetained :
  Processing.expectedERICMetadataCount ≡ 43996
metadataUniverseRetained = refl

data RegistryOccurrenceImpliesUniquePublication : Set where
data CandidatePNFImpliesReviewedEvidence : Set where
data MetadataRecordImpliesStudyReconstruction : Set where
data StudyProfileImpliesSourceSpanAdmission : Set where

registryOccurrencesNotAutomaticallyUnique :
  RegistryOccurrenceImpliesUniquePublication → ⊥
registryOccurrencesNotAutomaticallyUnique ()

candidatePNFNotReviewed :
  CandidatePNFImpliesReviewedEvidence → ⊥
candidatePNFNotReviewed ()

metadataNotWorldReconstruction :
  MetadataRecordImpliesStudyReconstruction → ⊥
metadataNotWorldReconstruction ()

studyProfileDoesNotAdmitSpan :
  StudyProfileImpliesSourceSpanAdmission → ⊥
studyProfileDoesNotAdmitSpan ()
