module DASHI.Wikimedia.IbrahimSnowballOpenScienceTransparencyAuditabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballPreregistrationReportingBiasProtocolDriftBidiExact as Registration
import DASHI.Wikimedia.IbrahimSnowballReplicationSourceGenealogyEvidenceSynthesisBidiExact as Genealogy
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Memory

------------------------------------------------------------------------
-- IBRAHIM / OPEN SCIENCE / TRANSPARENCY / AUDITABILITY BIDI
--
-- Openness can make methods, data, code and provenance inspectable.  That is
-- valuable, but inspectability is not definitionally reproducibility,
-- independent replication, evidentiary adequacy, ethical permissibility or
-- proposition truth.  This owner records that surviving distinction and feeds
-- it back into Science, Information, Memory and Governance parent nodes.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim open-science/transparency/auditability BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-15; identity does not create reproducibility, independence, audit success, ethical permission or truth")

openScienceQid : Identity.ExternalIdentityDemand
openScienceQid = mkQid "open science" "Q309823"

openDataQid : Identity.ExternalIdentityDemand
openDataQid = mkQid "open data" "Q309901"

openScienceDataQid : Identity.ExternalIdentityDemand
openScienceDataQid = mkQid "open science data / open research data" "Q17072965"

fairDataQid : Identity.ExternalIdentityDemand
fairDataQid = mkQid "FAIR data" "Q29032648"

fairPrinciplesQid : Identity.ExternalIdentityDemand
fairPrinciplesQid = mkQid "FAIR Data Principles" "Q29032644"

openScienceFrameworkQid : Identity.ExternalIdentityDemand
openScienceFrameworkQid = mkQid "Open Science Framework" "Q18691678"

openCodeQid : Identity.ExternalIdentityDemand
openCodeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim open-science/transparency/auditability BIDI"
  "external concept identity"
  "open research code / analysis-code sharing"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single concept QID safely promoted; software openness, source-code publication and research-analysis code remain consumer-distinct")

openMaterialsQid : Identity.ExternalIdentityDemand
openMaterialsQid = Identity.mkOptionalIdentityDemand
  "Ibrahim open-science/transparency/auditability BIDI"
  "external concept identity"
  "open research materials"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single concept QID safely promoted; materials availability remains a source-role coordinate")

------------------------------------------------------------------------
-- Dewey remains navigation-only and unresolved unless inspected exactly.
------------------------------------------------------------------------

openScienceDewey : Dewey.DeweyCoordinate
openScienceDewey = Dewey.mkUnresolvedDewey
  "open science"
  "no exact inspected DDC value promoted in this pass"

openDataDewey : Dewey.DeweyCoordinate
openDataDewey = Dewey.mkUnresolvedDewey
  "open data / open research data"
  "no exact inspected DDC value promoted in this pass"

fairDataDewey : Dewey.DeweyCoordinate
fairDataDewey = Dewey.mkUnresolvedDewey
  "FAIR data"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- Source-bounded methodological / meta-research objects.
------------------------------------------------------------------------

wilkinsonFairSource : Attribution.AttributedSource
wilkinsonFairSource = Attribution.mkDOISource
  "Mark D. Wilkinson et al."
  "The FAIR Guiding Principles for scientific data management and stewardship"
  "Scientific Data 3, 160018"
  "2016"
  "10.1038/sdata.2016.18"
  "https://doi.org/10.1038/sdata.2016.18"
  Attribution.academicArticleSource
  "formal publication of the FAIR principles for findability, accessibility, interoperability and reusability; FAIRness improves data stewardship/reuse conditions but does not create proposition truth or independent replication"
  Attribution.publicAttribution

duddaOpenScienceInterventionSource : Attribution.AttributedSource
duddaOpenScienceInterventionSource = Attribution.mkDOISource
  "Leonie Dudda et al."
  "Open science interventions to improve reproducibility and replicability of research: a scoping review"
  "Royal Society Open Science 12, 242057"
  "2025"
  "10.1098/rsos.242057"
  "https://doi.org/10.1098/rsos.242057"
  Attribution.academicArticleSource
  "scoping review finding that many open-science interventions are evaluated through proxy transparency/sharing outcomes and that direct evidence for improved reproducibility/replicability remains limited in many areas"
  Attribution.publicAttribution

klebelOpenScienceImpactSource : Attribution.AttributedSource
klebelOpenScienceImpactSource = Attribution.mkDOISource
  "Thomas Klebel; Vincent Traag; Ioanna Grypari; Lennart Stoy; Tony Ross-Hellauer"
  "The academic impact of Open Science: a scoping review"
  "Royal Society Open Science 12, 241248"
  "2025"
  "10.1098/rsos.241248"
  "https://doi.org/10.1098/rsos.241248"
  Attribution.academicArticleSource
  "scoping review of academic impacts of open access/data/code/evaluation/citizen-science practices; reports mixed and domain-dependent impacts including equity/resource constraints, so open-science status is not a universal quality certificate"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Existing owners reused: no parallel transparency or provenance calculus.
------------------------------------------------------------------------

registrationBoundary : Registration.PreregistrationReportingBiasBoundary
registrationBoundary = Registration.canonicalPreregistrationReportingBiasBoundary

genealogyBoundary : Genealogy.ReplicationSourceGenealogyEvidenceSynthesisBoundary
genealogyBoundary = Genealogy.canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary

memoryBoundary : Memory.LearningMemoryTraumaReplicationConsensusBoundary
memoryBoundary = Memory.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- Regression 1: open-science label cannot recover reproducibility outcome.
------------------------------------------------------------------------

data OpenScienceCase : Set where
  sameOpenScienceSurfaceReproducible sameOpenScienceSurfaceNotReproduced : OpenScienceCase

data OpenScienceSurface : Set where sameOpenScienceLabel : OpenScienceSurface
data ReproducibilityStatus : Set where reproductionObserved reproductionNotEstablished : ReproducibilityStatus

openScienceSurface : OpenScienceCase → OpenScienceSurface
openScienceSurface _ = sameOpenScienceLabel

reproducibilityStatus : OpenScienceCase → ReproducibilityStatus
reproducibilityStatus sameOpenScienceSurfaceReproducible = reproductionObserved
reproducibilityStatus sameOpenScienceSurfaceNotReproduced = reproductionNotEstablished

openScienceReproducibilityDefect : INF.NonFactorabilityWitness openScienceSurface reproducibilityStatus
openScienceReproducibilityDefect = INF.nonFactorabilityWitness
  sameOpenScienceSurfaceReproducible sameOpenScienceSurfaceNotReproduced refl (λ ())

openScienceLabelCannotFactorReproducibility :
  INF.FactorsThrough openScienceSurface reproducibilityStatus → ⊥
openScienceLabelCannotFactorReproducibility =
  INF.witnessRulesOutEveryFlatFactorisation openScienceReproducibilityDefect

------------------------------------------------------------------------
-- Regression 2: data availability cannot recover actual reusability/adequacy.
------------------------------------------------------------------------

data OpenDataCase : Set where
  sameOpenDataAvailableReusable sameOpenDataAvailableInsufficientMetadata : OpenDataCase

data OpenDataSurface : Set where sameDataAvailable : OpenDataSurface
data ReuseStatus : Set where reusableForConsumer notReusableForConsumer : ReuseStatus

openDataSurface : OpenDataCase → OpenDataSurface
openDataSurface _ = sameDataAvailable

reuseStatus : OpenDataCase → ReuseStatus
reuseStatus sameOpenDataAvailableReusable = reusableForConsumer
reuseStatus sameOpenDataAvailableInsufficientMetadata = notReusableForConsumer

openDataReuseDefect : INF.NonFactorabilityWitness openDataSurface reuseStatus
openDataReuseDefect = INF.nonFactorabilityWitness
  sameOpenDataAvailableReusable sameOpenDataAvailableInsufficientMetadata refl (λ ())

openDataAvailabilityCannotFactorConsumerReusability :
  INF.FactorsThrough openDataSurface reuseStatus → ⊥
openDataAvailabilityCannotFactorConsumerReusability =
  INF.witnessRulesOutEveryFlatFactorisation openDataReuseDefect

------------------------------------------------------------------------
-- Regression 3: FAIR/transparent carrier cannot recover proposition truth.
------------------------------------------------------------------------

data FairCase : Set where
  sameFairCarrierClaimTrue sameFairCarrierClaimFalse : FairCase

data FairSurface : Set where sameFairDataSurface : FairSurface
data ClaimTruth : Set where claimTrue claimFalse : ClaimTruth

fairSurface : FairCase → FairSurface
fairSurface _ = sameFairDataSurface

claimTruth : FairCase → ClaimTruth
claimTruth sameFairCarrierClaimTrue = claimTrue
claimTruth sameFairCarrierClaimFalse = claimFalse

fairTruthDefect : INF.NonFactorabilityWitness fairSurface claimTruth
fairTruthDefect = INF.nonFactorabilityWitness
  sameFairCarrierClaimTrue sameFairCarrierClaimFalse refl (λ ())

fairDataCannotFactorTruth : INF.FactorsThrough fairSurface claimTruth → ⊥
fairDataCannotFactorTruth = INF.witnessRulesOutEveryFlatFactorisation fairTruthDefect

------------------------------------------------------------------------
-- Regression 4: rerunning shared open artefacts cannot recover independent
-- replication. Reproduction of the same code/data is distinct from a new
-- evidentiary genealogy, just as equal public memory surface can hide a common
-- latent generation path.
------------------------------------------------------------------------

data AuditCase : Set where
  sameRerunOutputSharedArtifacts sameRerunOutputIndependentAcquisition : AuditCase

data RerunSurface : Set where sameSuccessfullyReexecutedOutput : RerunSurface
data IndependenceStatus : Set where sharedArtifactReproduction independentReplication : IndependenceStatus

rerunSurface : AuditCase → RerunSurface
rerunSurface _ = sameSuccessfullyReexecutedOutput

independenceStatus : AuditCase → IndependenceStatus
independenceStatus sameRerunOutputSharedArtifacts = sharedArtifactReproduction
independenceStatus sameRerunOutputIndependentAcquisition = independentReplication

rerunIndependenceDefect : INF.NonFactorabilityWitness rerunSurface independenceStatus
rerunIndependenceDefect = INF.nonFactorabilityWitness
  sameRerunOutputSharedArtifacts sameRerunOutputIndependentAcquisition refl (λ ())

successfulRerunCannotFactorIndependentReplication :
  INF.FactorsThrough rerunSurface independenceStatus → ⊥
successfulRerunCannotFactorIndependentReplication =
  INF.witnessRulesOutEveryFlatFactorisation rerunIndependenceDefect

------------------------------------------------------------------------
-- Regression 5: openness cannot recover ethical/publication permission.
------------------------------------------------------------------------

data EthicsCase : Set where
  sameOpenCarrierPermissionPaid sameOpenCarrierPermissionNotPaid : EthicsCase

data OpenCarrierSurface : Set where samePubliclyAccessibleCarrier : OpenCarrierSurface
data PermissionStatus : Set where ethicalPermissionPaid ethicalPermissionOpen : PermissionStatus

openCarrierSurface : EthicsCase → OpenCarrierSurface
openCarrierSurface _ = samePubliclyAccessibleCarrier

permissionStatus : EthicsCase → PermissionStatus
permissionStatus sameOpenCarrierPermissionPaid = ethicalPermissionPaid
permissionStatus sameOpenCarrierPermissionNotPaid = ethicalPermissionOpen

openEthicsDefect : INF.NonFactorabilityWitness openCarrierSurface permissionStatus
openEthicsDefect = INF.nonFactorabilityWitness
  sameOpenCarrierPermissionPaid sameOpenCarrierPermissionNotPaid refl (λ ())

publicAvailabilityCannotFactorEthicalPermission :
  INF.FactorsThrough openCarrierSurface permissionStatus → ⊥
publicAvailabilityCannotFactorEthicalPermission =
  INF.witnessRulesOutEveryFlatFactorisation openEthicsDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parents.
------------------------------------------------------------------------

record OpenScienceReverseConstraint : Set where
  constructor open-science-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open OpenScienceReverseConstraint public

scienceConstraint : OpenScienceReverseConstraint
scienceConstraint = open-science-reverse-constraint
  "Science / reproducibility"
  "openness, transparency, FAIRness, executability, reproducibility, independent replication, uncertainty and truth remain distinct"
  false

informationConstraint : OpenScienceReverseConstraint
informationConstraint = open-science-reverse-constraint
  "Information / data stewardship"
  "availability, findability, metadata quality, interoperability, licence/permission, consumer reusability and evidentiary adequacy remain distinct"
  false

memoryConstraint : OpenScienceReverseConstraint
memoryConstraint = open-science-reverse-constraint
  "Memory / learning / public surface"
  "visible/public output, latent generation history, common-source dependence, retrieval/update history and independent reacquisition remain distinct"
  false

governanceConstraint : OpenScienceReverseConstraint
governanceConstraint = open-science-reverse-constraint
  "Governance / ethics / affected subjects"
  "technical openness, participant consent, privacy, Indigenous/community authority, legal permission and publication permissibility remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data OpenScienceMeansReproducible : Set where
data OpenDataMeansReusable : Set where
data FairMeansTrue : Set where
data SuccessfulRerunMeansIndependentReplication : Set where
data PublicMeansEthicallyShareable : Set where
data QidMeansQuality : Set where
data DeweyMeansMethodQuality : Set where

openScienceDoesNotMeanReproducible : OpenScienceMeansReproducible → ⊥
openScienceDoesNotMeanReproducible ()

openDataDoesNotMeanReusable : OpenDataMeansReusable → ⊥
openDataDoesNotMeanReusable ()

fairDoesNotMeanTrue : FairMeansTrue → ⊥
fairDoesNotMeanTrue ()

successfulRerunDoesNotMeanIndependentReplication : SuccessfulRerunMeansIndependentReplication → ⊥
successfulRerunDoesNotMeanIndependentReplication ()

publicDoesNotMeanEthicallyShareable : PublicMeansEthicallyShareable → ⊥
publicDoesNotMeanEthicallyShareable ()

qidDoesNotCreateQuality : QidMeansQuality → ⊥
qidDoesNotCreateQuality ()

deweyDoesNotCreateMethodQuality : DeweyMeansMethodQuality → ⊥
deweyDoesNotCreateMethodQuality ()

record OpenScienceTransparencyAuditabilityBoundary : Set where
  constructor open-science-transparency-auditability-boundary
  field
    safeQidsAttached : Bool
    unresolvedExactOpenCodeMaterialsQidsRetained : Bool
    deweyUnresolvedRetained : Bool
    doiSourceRolesRetained : Bool
    openScienceSeparatedFromReproducibility : Bool
    openDataSeparatedFromConsumerReusability : Bool
    fairSeparatedFromTruth : Bool
    rerunSeparatedFromIndependentReplication : Bool
    opennessSeparatedFromEthicalPermission : Bool
    preregistrationAndGenealogyOwnersReused : Bool
    memoryHyperfabricPublicSurfaceAnalogyReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open OpenScienceTransparencyAuditabilityBoundary public

canonicalOpenScienceTransparencyAuditabilityBoundary :
  OpenScienceTransparencyAuditabilityBoundary
canonicalOpenScienceTransparencyAuditabilityBoundary =
  open-science-transparency-auditability-boundary
    true true true true true true true true true true true true false
