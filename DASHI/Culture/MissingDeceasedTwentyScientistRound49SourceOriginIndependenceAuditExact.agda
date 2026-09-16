module DASHI.Culture.MissingDeceasedTwentyScientistRound49SourceOriginIndependenceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound48AntiEchoChamberMethodologyExact as R48

------------------------------------------------------------------------
-- ROUND 49: SOURCE-ORIGIN / INDEPENDENCE AUDIT
--
-- Anti-echo-chamber application to the Chinese nine-person cluster narrative.
-- External publication is paid; independent origin is not silently assumed.
------------------------------------------------------------------------

data ExternalClusterIndependenceStatus : Set where
  singleExternalCompilation : ExternalClusterIndependenceStatus
  dependentRestatement : ExternalClusterIndependenceStatus
  independenceUnresolved : ExternalClusterIndependenceStatus
  independentlyAssembled : ExternalClusterIndependenceStatus

record ClusterSourceOriginReceipt : Set where
  constructor cluster-source-origin-receipt
  field
    outlet : String
    publicationDate : String
    clusterReference : String
    underlyingSourceReference : String
    independenceStatus : ExternalClusterIndependenceStatus
    paysExternalAssembly : Bool
    paysIndependentAssembly : Bool
    sourceBoundary : String

open ClusterSourceOriginReceipt public

indiaTodayCluster : ClusterSourceOriginReceipt
indiaTodayCluster = cluster-source-origin-receipt
  "India Today"
  "2026-04-24"
  "20 scientists die or vanish across US, China: What's happening?"
  "article explicitly draws individual-case details from Chinese obituaries/reporting, EET China/ScienceNet and SCMP among other reported surfaces"
  singleExternalCompilation
  true false
  "Pays an externally assembled Chinese comparison cohort; because the article itself cites upstream Chinese/Hong Kong sources, those underlying case reports are not additional independent cluster assemblies."

newsNationCluster : ClusterSourceOriginReceipt
newsNationCluster = cluster-source-origin-receipt
  "NewsNation / Morning in America"
  "2026-04-24"
  "Deaths of Chinese scientists spark questions of US link"
  "currently acquired public surface confirms a similar Chinese cluster framing but does not establish whether its list was assembled independently of India Today or a shared upstream source"
  independenceUnresolved
  true false
  "Pays a second outlet carrying the cluster narrative; independent source origin remains unresolved until its sourcing chain is acquired."

chinaClusterExternallyAssembledPaid : Bool
chinaClusterExternallyAssembledPaid = true

chinaClusterIndependentlyAssembledPaid : Bool
chinaClusterIndependentlyAssembledPaid = false

indiaTodayUsesUnderlyingChineseAndSCMPSources : Bool
indiaTodayUsesUnderlyingChineseAndSCMPSources = true

newsNationIndependenceFromIndiaTodayUnresolved : Bool
newsNationIndependenceFromIndiaTodayUnresolved = true

repeatedClusterNarrativeCannotMultiplyIndependentEvidence : Bool
repeatedClusterNarrativeCannotMultiplyIndependentEvidence = true

externalCoverageClaimRequiresIndependenceQualification : Bool
externalCoverageClaimRequiresIndependenceQualification = true

foreignInstitutionalCaseReportsRemainUsefulIndependentlyOfClusterOrigin : Bool
foreignInstitutionalCaseReportsRemainUsefulIndependentlyOfClusterOrigin = true

sourceOriginAuditMayLowerNarrativeConfidence : Bool
sourceOriginAuditMayLowerNarrativeConfidence = true

sourceOriginAuditMayNotErasePaidUnderlyingFacts : Bool
sourceOriginAuditMayNotErasePaidUnderlyingFacts = true

round49CorrectedNarrative : String
round49CorrectedNarrative = "The nine-person Chinese scientist cluster is externally assembled and independently checkable at the level of many underlying individual cases. However, the current evidence does not yet establish that multiple outlets independently assembled the same nine-person cluster from separate origins. India Today's compilation explicitly relies on upstream Chinese/Hong Kong case reporting, and NewsNation's independence from that compilation or a shared upstream source remains unresolved. Therefore source-count cannot be used as an independence count."

round49H2PaidCount : Nat
round49H2PaidCount = 0

round49H3PaidCount : Nat
round49H3PaidCount = 0

round49Pareto : String
round49Pareto = "Trace the first-publication/source-origin chain for the Chinese cluster itself, while separately preserving direct institutional evidence for each person's identity, death and technical role. Prefer first-party obituaries, university/CAS notices and exact technical records; treat syndicated or derivative cluster stories as one origin family unless independence is positively established."
