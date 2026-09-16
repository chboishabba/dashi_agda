module DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Prior

------------------------------------------------------------------------
-- PRIMARY-SOURCE EXTENSION ATLAS FOR THE MANUSCRIPT/METHOD TRANCHE
--
-- Only genuinely new source objects live here. Existing call, Charter, LCA,
-- circularity, participatory and longitudinal sources remain owned by their
-- prior canonical atlases and are imported rather than duplicated.
------------------------------------------------------------------------

unescoESD2030RoadmapSource : Attr.AttributedSource
unescoESD2030RoadmapSource =
  Attr.mkNoDOISource
    "UNESCO"
    "Education for sustainable development: a roadmap"
    "UNESCO"
    "2020"
    "https://www.unesco.org/en/articles/education-sustainable-development-roadmap"
    Attr.institutionalSource
    "Primary UNESCO implementation framework for ESD for 2030. Supports five priority action areas and the system-transformation framing; it is normative/programmatic guidance, not evidence that a named digital intervention achieved transformation."
    Attr.publicAttribution

unescoESD2030MidtermSource : Attr.AttributedSource
unescoESD2030MidtermSource =
  Attr.mkNoDOISource
    "Simon Broek; Anahat Kaur; Ockham IPS (Netherlands); UNESCO"
    "Mid-term evaluation of the ESD for 2030 framework, 2021-2024"
    "UNESCO"
    "2026"
    "https://www.unesco.org/en/articles/mid-term-evaluation-esd-2030-framework-2021-2024"
    Attr.institutionalSource
    "Primary institutional evaluation of ESD-for-2030 implementation. Supports the source-bounded observation that substantial activity can coexist with limited systemic transformation and recommendations for stronger coherence, monitoring and national ownership; does not evaluate this manuscript's proposed digital-ESD framework."
    Attr.publicAttribution

oecdDigitalEducationOutlook2026Source : Attr.AttributedSource
oecdDigitalEducationOutlook2026Source =
  Attr.mkDOISource
    "OECD"
    "OECD Digital Education Outlook 2026: Exploring Effective Uses of Generative AI in Education"
    "OECD Publishing"
    "2026"
    "10.1787/062a7394-en"
    "https://www.oecd.org/en/publications/oecd-digital-education-outlook-2026_062a7394-en.html"
    Attr.institutionalSource
    "Primary OECD synthesis/report for current digital/GenAI education policy and evidence. Supports the distinction between task performance and learning, and the need for pedagogical guidance, human-centred design, research, governance and enabling infrastructure; it does not establish sustainability or learning effects for every technology or context."
    Attr.publicAttribution

unescoAICommonGoodMinisterialSource : Attr.AttributedSource
unescoAICommonGoodMinisterialSource =
  Attr.mkNoDOISource
    "Education ministers and designated representatives convened by UNESCO"
    "Ministerial Statement: Sustaining education as a common good in the age of AI"
    "UNESCO Digital Learning Week 2026"
    "2026"
    "https://www.unesco.org/en/articles/education-ministers-call-education-remain-common-good-age-ai-unescos-digital-learning-week"
    Attr.institutionalSource
    "Primary intergovernmental normative/governance source adopted during UNESCO Digital Learning Week 2026. Supports deliberative governance, public accountability, learner/teacher rights and source-bounded procurement/infrastructure principles including total-cost-of-ownership, interoperability, portability and open systems; it is not evidence that any named AI or digital-education intervention is effective or sustainable."
    Attr.publicAttribution

unescoAICommonGoodDiscussionSource : Attr.AttributedSource
unescoAICommonGoodDiscussionSource =
  Attr.mkNoDOISource
    "UNESCO"
    "Sustaining education as a common good in the age of AI: The case for deliberative governance"
    "UNESCO global consultation on education in the age of AI"
    "2026"
    "https://www.unesco.org/en/digital-education/artificial-intelligence/consultation"
    Attr.institutionalSource
    "Primary UNESCO discussion-paper/consultation source. It frames deliberative governance and six directional shifts for public consultation feeding future policy briefs; it is not the adopted ministerial statement, settled policy, intervention evidence, or proof that consultation recommendations have been implemented."
    Attr.publicAttribution

primaryMethodologySourceAtlas : Attr.AttributedSourceAtlas
primaryMethodologySourceAtlas =
  Attr.mkSourceAtlas
    "digital ESD manuscript primary-source methodology extension"
    "DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact"
    ( unescoESD2030RoadmapSource
    ∷ unescoESD2030MidtermSource
    ∷ oecdDigitalEducationOutlook2026Source
    ∷ unescoAICommonGoodMinisterialSource
    ∷ unescoAICommonGoodDiscussionSource
    ∷ [] )
    "Primary institutional sources for ESD system transformation, current digital-education conditions and 2026 AI-era public-purpose governance. The adopted ministerial statement and consultation discussion paper remain distinct source roles. Existing UNESCO-UNICEF-ITU Charter, ITU lifecycle/circularity methods and other evidence remain in the prior acquisition atlas; this extension does not duplicate them."

unescoRoadmapSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt unescoESD2030RoadmapSource
unescoRoadmapSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt unescoESD2030RoadmapSource

unescoMidtermSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt unescoESD2030MidtermSource
unescoMidtermSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt unescoESD2030MidtermSource

oecdOutlookSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt oecdDigitalEducationOutlook2026Source
oecdOutlookSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt oecdDigitalEducationOutlook2026Source

unescoAICommonGoodMinisterialSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt unescoAICommonGoodMinisterialSource
unescoAICommonGoodMinisterialSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt unescoAICommonGoodMinisterialSource

unescoAICommonGoodDiscussionSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt unescoAICommonGoodDiscussionSource
unescoAICommonGoodDiscussionSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt unescoAICommonGoodDiscussionSource

priorAcquisitionAtlasRetained : Prior.DigitalESDAcquisitionAtlas
priorAcquisitionAtlasRetained = Prior.canonicalDigitalESDAcquisitionAtlas

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data InstitutionalFrameworkCreatesInterventionEffect : Set where
data MidtermProgrammeEvaluationCreatesLocalCausalEffect : Set where
data DigitalEducationOutlookCreatesSustainabilityProof : Set where
data MinisterialGovernanceSourceCreatesInterventionEffect : Set where
data ConsultationDiscussionCreatesAdoptedPolicy : Set where

institutionalFrameworkDoesNotCreateInterventionEffect :
  InstitutionalFrameworkCreatesInterventionEffect → ⊥
institutionalFrameworkDoesNotCreateInterventionEffect ()

midtermEvaluationDoesNotCreateLocalCausalEffect :
  MidtermProgrammeEvaluationCreatesLocalCausalEffect → ⊥
midtermEvaluationDoesNotCreateLocalCausalEffect ()

digitalEducationOutlookDoesNotCreateSustainabilityProof :
  DigitalEducationOutlookCreatesSustainabilityProof → ⊥
digitalEducationOutlookDoesNotCreateSustainabilityProof ()

ministerialGovernanceSourceDoesNotCreateInterventionEffect :
  MinisterialGovernanceSourceCreatesInterventionEffect → ⊥
ministerialGovernanceSourceDoesNotCreateInterventionEffect ()

consultationDiscussionDoesNotCreateAdoptedPolicy :
  ConsultationDiscussionCreatesAdoptedPolicy → ⊥
consultationDiscussionDoesNotCreateAdoptedPolicy ()

record PrimarySourceMethodologyBoundary : Set where
  constructor primary-source-methodology-boundary
  field
    primaryInstitutionalSourcesAttributed : Bool
    primaryInstitutionalSourcesAttributedIsTrue :
      primaryInstitutionalSourcesAttributed ≡ true
    priorAtlasRetainedWithoutDuplication : Bool
    priorAtlasRetainedWithoutDuplicationIsTrue :
      priorAtlasRetainedWithoutDuplication ≡ true
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false
    institutionalReportCreatesSameObjectInterventionEffect : Bool
    institutionalReportCreatesSameObjectInterventionEffectIsFalse :
      institutionalReportCreatesSameObjectInterventionEffect ≡ false
    ministerialGovernanceSourceCreatesInterventionEffect : Bool
    ministerialGovernanceSourceCreatesInterventionEffectIsFalse :
      ministerialGovernanceSourceCreatesInterventionEffect ≡ false
    consultationDiscussionCreatesAdoptedPolicy : Bool
    consultationDiscussionCreatesAdoptedPolicyIsFalse :
      consultationDiscussionCreatesAdoptedPolicy ≡ false

open PrimarySourceMethodologyBoundary public

canonicalPrimarySourceMethodologyBoundary : PrimarySourceMethodologyBoundary
canonicalPrimarySourceMethodologyBoundary =
  primary-source-methodology-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
