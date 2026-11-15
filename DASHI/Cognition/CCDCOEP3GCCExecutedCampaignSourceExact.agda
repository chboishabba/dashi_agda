module DASHI.Cognition.CCDCOEP3GCCExecutedCampaignSourceExact where

------------------------------------------------------------------------
-- GCC / E. Bruce Harrison executed-communications case, 1993-1995.
-- Original published PR company case history preserved by Climate Files:
-- https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/one-pager-from-e-bruce-harrisons-pr-company-undated/
-- Undated; archive estimates 1994-95. Source documents a firm's own
-- description of its campaign AND its self-attributed successes.
-- The firm's assertions are not observational impact estimates.
--
-- Separately archived GCC-held 1993 media clippings:
-- https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/1993-media-hits/
-- Clippings provide source-located media objects, not a complete sample.
-- Brulle 2022 DOI 10.1080/09644016.2022.2058815 is independent analysis.
-- 2021 Supran/Oreskes ExxonMobil corpus, DOI
-- 10.1016/j.oneear.2021.04.014, is a SEPARATE replication cohort.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as D

data EvidenceObject : Set where
  harrisonFirmCaseHistory : EvidenceObject
  gccHeldMediaClippings1993 : EvidenceObject
  brulleHistoricalReview2022 : EvidenceObject
  exxonRhetoricCorpus2021 : EvidenceObject
  apiProposedPlan1998 : EvidenceObject

data EvidenceKind : Set where
  agencyCampaignAccount : EvidenceKind
  preservedMediaObjects : EvidenceKind
  scholarlyHistoricalSynthesis : EvidenceKind
  documentCorpusAnalysis : EvidenceKind
  proposedUnapprovedPlan : EvidenceKind

kind : EvidenceObject → EvidenceKind
kind harrisonFirmCaseHistory = agencyCampaignAccount
kind gccHeldMediaClippings1993 = preservedMediaObjects
kind brulleHistoricalReview2022 = scholarlyHistoricalSynthesis
kind exxonRhetoricCorpus2021 = documentCorpusAnalysis
kind apiProposedPlan1998 = proposedUnapprovedPlan

data StatementRole : Set where
  statedCampaignTactic : StatementRole
  firmClaimsImpact : StatementRole
  archivedMediaAppearance : StatementRole
  independentlyMeasuredChange : StatementRole

data HarrisonStatement : Set where
  mediaTours : HarrisonStatement
  editorialBoardVisits : HarrisonStatement
  opEdsAndExperts : HarrisonStatement
  monthlyNewsletters : HarrisonStatement
  claimedMediaTurnaround : HarrisonStatement
  claimedCarbonTaxInfluence : HarrisonStatement
  claimedVoluntaryPolicyInfluence : HarrisonStatement

harrisonStatementRole : HarrisonStatement → StatementRole
harrisonStatementRole mediaTours = statedCampaignTactic
harrisonStatementRole editorialBoardVisits = statedCampaignTactic
harrisonStatementRole opEdsAndExperts = statedCampaignTactic
harrisonStatementRole monthlyNewsletters = statedCampaignTactic
harrisonStatementRole claimedMediaTurnaround = firmClaimsImpact
harrisonStatementRole claimedCarbonTaxInfluence = firmClaimsImpact
harrisonStatementRole claimedVoluntaryPolicyInfluence = firmClaimsImpact

-- The recorded outcome ASSERTION is exactly a firm's self-evaluation,
-- not a witnessed shift in an externally sampled media time series.
-- In particular there is no constructor here for a measured causal
-- impact; that requires separate raw outlet/time/source observations.
data GCCOutcomeStatus : Set where
  selfClaimOnly : GCCOutcomeStatus
  sourceArchivedAppearance : GCCOutcomeStatus
  independentCausalEstimateNotAdmitted : GCCOutcomeStatus

reportedTurnaroundStatus : GCCOutcomeStatus
reportedTurnaroundStatus = selfClaimOnly

data MediaObject : Set where
  washingtonPostJuly1993 : MediaObject
  nashvilleBannerChristy1993 : MediaObject

mediaObjectHasIndependentEffectReceipt : MediaObject → Bool
mediaObjectHasIndependentEffectReceipt _ = false

mediaObjectsInArchivedIndex : List MediaObject
mediaObjectsInArchivedIndex =
  washingtonPostJuly1993 ∷ nashvilleBannerChristy1993 ∷ []

archivedMediaDoesNotEstablishEffect :
  (o : MediaObject) →
  mediaObjectHasIndependentEffectReceipt o ≡ false
archivedMediaDoesNotEstablishEffect washingtonPostJuly1993 = refl
archivedMediaDoesNotEstablishEffect nashvilleBannerChristy1993 = refl

-- Identically broad "climate communication" labels cannot transport
-- original evidentiary grades between agency claims and independent
-- newspaper archive holdings.
data GenericTopic : Set where
  climateCommunications : GenericTopic

flatten : EvidenceObject → GenericTopic
flatten _ = climateCommunications

caseHistoryIsNotMediaArchive :
  kind harrisonFirmCaseHistory ≡ kind gccHeldMediaClippings1993 → ⊥
caseHistoryIsNotMediaArchive ()

evidenceKindDoesNotFactorThroughGenericTopic :
  NF.FactorsThrough flatten kind → ⊥
evidenceKindDoesNotFactorThroughGenericTopic =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      harrisonFirmCaseHistory gccHeldMediaClippings1993
      refl caseHistoryIsNotMediaArchive)

sourceIdentityProbe : D.ExperimentBundle EvidenceObject
sourceIdentityProbe =
  D.experimentBundle
    EvidenceKind kind 1
    "Distinguish original PR self-report, archived newspaper item, review and proposed plan"
    "Source types are located; outlet-level effect data and errors remain OPEN"

sourceIdentitySeparates :
  D.BundleSeparates sourceIdentityProbe
    harrisonFirmCaseHistory gccHeldMediaClippings1993
sourceIdentitySeparates =
  D.bundleSeparates caseHistoryIsNotMediaArchive

sourceIdentityExtension :
  D.DiscriminatingLanguageExtension flatten
sourceIdentityExtension =
  D.discriminatingLanguageExtension
    (D.currentObserverCollision
      harrisonFirmCaseHistory gccHeldMediaClippings1993 refl)
    sourceIdentityProbe sourceIdentitySeparates

-- The real source observations make different WHO/WHEN/WHAT claims.
-- No group-similarity inference links the original GCC events to the
-- unapproved April 1998 API plan, and no 2021 ExxonMobil document
-- is placed into the 1993 newspaper-clipping sample.
data StudyCohort : Set where
  gccAgencyAndMedia1993to1995 : StudyCohort
  exxon180Documents2021 : StudyCohort

data PooledTreatmentReceipt : Set where

noAutomaticPoolOfDistinctCohorts : PooledTreatmentReceipt → ⊥
noAutomaticPoolOfDistinctCohorts ()

-- Sourced outcome measurement only after materialisation, item-specific
-- claim coding, temporal baseline, comparison and audit receipts.
record GCCMediaReplicationGate : Set where
  constructor gccMediaReplicationGate
  field
    archivedOriginalBytesPresent : Bool
    datedOutletSampleComplete : Bool
    codedActualArticleText : Bool
    preInterventionBaselinePresent : Bool
    comparisonAndUncertaintyPresent : Bool
    causalEffectAdmitted : Bool

selectedGCCCaseGate : GCCMediaReplicationGate
selectedGCCCaseGate =
  gccMediaReplicationGate false false false false false false

noInventedCausalEstimate :
  GCCMediaReplicationGate.causalEffectAdmitted selectedGCCCaseGate
  ≡ false
noInventedCausalEstimate = refl

data ExxonReplicationAccess : Set where
  supplementaryCatalogLinked : ExxonReplicationAccess
  depositedDatasetRestricted : ExxonReplicationAccess
  full180DocumentReanalysisCompleted : ExxonReplicationAccess

selectedExxonAccess : ExxonReplicationAccess
selectedExxonAccess = depositedDatasetRestricted
