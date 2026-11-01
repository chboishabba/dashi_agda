module DASHI.Governance.AICaptureEpsteinTechEvidenceBridge20261101Exact where

------------------------------------------------------------------------
-- EPSTEIN / TECH RESEARCH / POLITICAL FINANCE: EVIDENCE-GRADED EDGE TYPES
--
-- Prior original owners:
-- DASHI.Governance.EvidenceGradedGenealogyCore (grade A-E and paths);
-- DASHI.Reasoning.ReleasedArtifactProvenanceBidiExact (DOJ disclosure
-- != institutional authorship/validation);
-- DASHI governance epistemic/Thiel actor and source atlas.
-- Earlier open Epstein research PRs #1131/#1245 keep their case-specific
-- evidence. No unmerged source is duplicated.
--
-- Bounded sources: original DOJ EFTA02587213-EFTA02587214 chain; WIRED
-- tech-elite released-record survey 2026-02; SCMP 2026-02 OpenCog
-- funding review; DOJ EFTA00587395 incomplete draft, not wire receipt.
-- No contact/e-mail/funding is proof of involvement in Epstein's crimes,
-- present-day government command or any specific AI policy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Governance.EvidenceGradedGenealogyCore as Evidence
import DASHI.Reasoning.ReleasedArtifactProvenanceBidiExact as Released
import DASHI.Governance.KnowledgeProcessingCaptureSourceAtlas20261101Exact as Atlas
import DASHI.Governance.ThielAntichristPoliticalTheology20261101Exact as Thiel

data EvidenceCase : Set where
  epsteinThielOriginalEmail
  thielEpsteinReportedMeetings
  epsteinOpenCogReportedSupport
  blackHumanityPlusUnsignedDraft : EvidenceCase

data DistinctActivity : Set where
  directCorrespondence
  reportedInPersonContact
  reportedResearchFunding
  unsignedDonationProposal : DistinctActivity

edgeType : EvidenceCase → DistinctActivity
edgeType epsteinThielOriginalEmail = directCorrespondence
edgeType thielEpsteinReportedMeetings = reportedInPersonContact
edgeType epsteinOpenCogReportedSupport = reportedResearchFunding
edgeType blackHumanityPlusUnsignedDraft = unsignedDonationProposal

grade : EvidenceCase → Evidence.EvidenceGrade
grade epsteinThielOriginalEmail = Evidence.gradeA
grade thielEpsteinReportedMeetings = Evidence.gradeB
grade epsteinOpenCogReportedSupport = Evidence.gradeB
grade blackHumanityPlusUnsignedDraft = Evidence.gradeC

source : EvidenceCase → Atlas.SourceReceipt
source epsteinThielOriginalEmail = Atlas.epsteinThiel2014Correspondence
source thielEpsteinReportedMeetings = Atlas.epsteinThielWiredResearch
source epsteinOpenCogReportedSupport = Atlas.goertzelEpsteinReporting
source blackHumanityPlusUnsignedDraft = Atlas.humanityPlusBlackDraft

-- A-grade refers ONLY to the text of correspondence, not completed travel,
-- a meeting with a proposed third party, a government policy, or culpability.
originalCorrespondenceGrade :
  grade epsteinThielOriginalEmail ≡ Evidence.gradeA
originalCorrespondenceGrade = refl

draftDoesNotBecomeStrongGenealogicalEdge :
  Evidence.StrongGrade (grade blackHumanityPlusUnsignedDraft) → ⊥
draftDoesNotBecomeStrongGenealogicalEdge =
  Evidence.gradeCIsNotStrong

releaseNotEquivalentToVerification :
  Released.presentInOfficialRelease ≡
  Released.verifiedByDisclosingInstitution → ⊥
releaseNotEquivalentToVerification = Released.releaseNotVerification

thielPalantirCorporateRelationIsSeparate :
  Thiel.DocumentedConnection
    Thiel.thiel Thiel.palantirInstitution
    Thiel.foundingCorporateConnection
thielPalantirCorporateRelationIsSeparate =
  Thiel.thielPalantirFounding

genealogyDoesNotGrantUniversalCommand :
  Evidence.OneStrongEdgeEstablishesUniversalNetwork → ⊥
genealogyDoesNotGrantUniversalCommand =
  Evidence.oneStrongEdgeDoesNotEstablishUniversalNetwork

data ProposalSameAsCompletedPayment : Set where
data NetworkContactEqualsSharedPolicyDoctrine : Set where

unsignedDraftNotSettlement : ProposalSameAsCompletedPayment → ⊥
unsignedDraftNotSettlement ()

historicalContactNotCommonDoctrine :
  NetworkContactEqualsSharedPolicyDoctrine → ⊥
historicalContactNotCommonDoctrine ()
