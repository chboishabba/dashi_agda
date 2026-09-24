module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound14Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Education.DigitalESDPhilosophySurveillanceAuditBoundaryExact as PhilosophyAudit

------------------------------------------------------------------------
-- ROUND 14: IDENTITY-SYSTEM LEGIBILITY / DEADNAME PROPAGATION / VISIBILITY RISK.
--
-- The post-Round-13 frontier still retains exclusion-by-design, disclosure and
-- category-definition debt. This round targets institutional information
-- systems where identity is made legible through chosen-name/pronoun/legal-name
-- fields, and where greater visibility can itself create surveillance/outness
-- risk. Identity support therefore cannot be represented as one monotone scalar.
------------------------------------------------------------------------

data Round14Residual : Set where
  pronounChosenNameVisibilitySurveillanceTradeoff : Round14Residual
  deadnamePropagationAcrossUniversitySystems : Round14Residual
  legalNameGateToInstitutionalIdentityChange : Round14Residual
  tgdOnlineEducationSafetySupportTradeoff : Round14Residual

record Round14Candidate : Set where
  constructor round14-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    targetResidual : Round14Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round14Candidate public

mkRound14Candidate :
  (source : Attr.AttributedSource) →
  Round14Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round14Candidate
mkRound14Candidate source residual lens reading limitation =
  round14-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound14Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 14"))
    residual lens reading limitation false refl

------------------------------------------------------------------------
-- University UX systems: chosen-name/pronoun legibility can also create risk.
------------------------------------------------------------------------

greenPronounUXSource : Attr.AttributedSource
greenPronounUXSource = Attr.mkDOISource
  "McKinley Green"
  "Trans and Queer Visibility in an Era of Hyper Surveillance: A User Experience Study of University Systems for Sharing Gender Pronouns"
  "Journal of Technical Writing and Communication 56(1), 35-60"
  "2026 issue / 2025 online"
  "10.1177/00472816251384913"
  "https://doi.org/10.1177/00472816251384913"
  Attr.academicArticleSource
  "User-experience study of college students navigating university-sponsored online systems for chosen-name and pronoun sharing. The study treats identity visibility as a usability/inclusion affordance that can simultaneously create surveillance and safety concerns when gender nonconformity becomes institutionally visible."
  Attr.publicAttribution

greenCandidate : Round14Candidate
greenCandidate = mkRound14Candidate
  greenPronounUXSource
  pronounChosenNameVisibilitySurveillanceTradeoff
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Direct identity-legibility x anti-panopticon source: more identity information in the institutional interface can improve recognition while also increasing involuntary visibility and surveillance exposure. The relevant consumer is therefore not maximised by visibility alone."
  "UX study and source-bounded trans/queer context; it does not establish a universal harm from pronoun fields or that reduced visibility is always safer or more inclusive."

------------------------------------------------------------------------
-- Chemistry graduate students: chosen-name fields fail downstream propagation.
------------------------------------------------------------------------

nolanBlytheVincentRuzSource : Attr.AttributedSource
nolanBlytheVincentRuzSource = Attr.mkDOISource
  "Michelle M. Nolan; Isaac M. Blythe; Paulette Vincent-Ruz"
  "The challenges of transgender and nonbinary graduate students in chemistry: A qualitative study on trans identity, science culture, and institutional support using reflexive thematic analysis"
  "PLOS ONE 20(4), e0320493"
  "2025"
  "10.1371/journal.pone.0320493"
  "https://doi.org/10.1371/journal.pone.0320493"
  Attr.academicArticleSource
  "Qualitative interview study of 10 transgender/nonbinary/two-spirit/gender-expansive chemistry PhD students. Participants described institutional systems in which chosen/preferred-name fields did not reliably propagate to academic records, email and online-learning systems; legal/dead names were exposed downstream and could involuntarily out students."
  Attr.publicAttribution

nolanCandidate : Round14Candidate
nolanCandidate = mkRound14Candidate
  nolanBlytheVincentRuzSource
  deadnamePropagationAcrossUniversitySystems
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Strong same-institution information-flow collision: the presence of a preferred-name input does not determine downstream identity representation. A nominally inclusive field can be erased by later system joins, making provenance/propagation part of accessibility and safety."
  "Ten chemistry doctoral students and qualitative evidence; downstream deadname exposure does not establish all university systems fail this way or a universal educational-outcome effect."

------------------------------------------------------------------------
-- UK higher education: legal-name gate to internal system/ID changes.
------------------------------------------------------------------------

reganUKTransHESource : Attr.AttributedSource
reganUKTransHESource = Attr.mkDOISource
  "Lynne Regan"
  "A Mixed Methods Investigation into the Experiences of Transgender Students in Higher Education in the UK"
  "Bulletin of Applied Transgender Studies 2(3-4), 195-222"
  "2023"
  "10.57814/8n20-g959"
  "https://doi.org/10.57814/8n20-g959"
  Attr.academicArticleSource
  "Mixed-method UK higher-education study with 166 survey respondents after exclusions and seven interviews across many institutions. Participants reported difficulties changing names/genders on university systems; three interviewees reported that legal name change was required before internal systems/ID cards could be changed, creating disclosure and outness trade-offs."
  Attr.publicAttribution

reganCandidate : Round14Candidate
reganCandidate = mkRound14Candidate
  reganUKTransHESource
  legalNameGateToInstitutionalIdentityChange
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Literal category/legibility gate: institutional systems may condition recognition of situated identity on a legal-document state. This makes legal identity, lived identity, system-visible identity and safe disclosure distinct coordinates rather than aliases."
  "Mixed-method sample and institution-specific experiences; a legal-name requirement in some institutions does not establish the policy of every UK HEI or determine one appropriate administrative solution."

------------------------------------------------------------------------
-- Australian TGD youth: online setting changes bullying/support/misgendering mix.
------------------------------------------------------------------------

fletcherJonesVanBergenSource : Attr.AttributedSource
fletcherJonesVanBergenSource = Attr.mkDOISource
  "Jessie Fletcher; Tiffany Jones; Penny Van Bergen"
  "Transgender and Gender Diverse (TGD) students and online education in Australia"
  "Children and Youth Services Review 172, 108258"
  "2025"
  "10.1016/j.childyouth.2025.108258"
  "https://doi.org/10.1016/j.childyouth.2025.108258"
  Attr.academicArticleSource
  "Open-access mixed quantitative/qualitative survey of 1,671 Australian TGD-identifying students aged 14-25, using a trans-informed design that prioritised self-identification and lived experience. Participants in alternative schooling often moved after bullying/poor mental health. In online settings physical bullying improved incidentally for some, while social support reduced and misgendering/deadnaming increased. More than one quarter lived in rural/remote areas and a substantial share reported neurodivergence."
  Attr.publicAttribution

fletcherCandidate : Round14Candidate
fletcherCandidate = mkRound14Candidate
  fletcherJonesVanBergenSource
  tgdOnlineEducationSafetySupportTradeoff
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "High-dimensional Australian intersectional source: educational delivery mode changes several safety/support coordinates in opposite directions, and the study's self-identification surface preserves gender diversity instead of forcing one binary category. It attacks exclusion, category-definition, future-option and disclosure/visibility fibres simultaneously."
  "Self-selected TGD sample recruited through social media/support organisations; online-education exposure partly reflects pandemic conditions. Reduced physical bullying does not make online education universally safer, and increased deadnaming/misgendering does not establish one causal platform mechanism."

canonicalRound14Frontier : List Round14Candidate
canonicalRound14Frontier =
  fletcherCandidate
  ∷ nolanCandidate
  ∷ reganCandidate
  ∷ greenCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / identity-legibility firewalls.
------------------------------------------------------------------------

data Round14CandidateCreatesIncludedStudy : Set where
data MoreIdentityVisibilityCreatesMoreSafety : Set where
data PreferredNameFieldCreatesDownstreamNameRespect : Set where
data LegalNameCreatesSituatedIdentityTruth : Set where
data OnlineSettingCreatesUniversalTGDInclusion : Set where

round14CandidateDoesNotCreateIncludedStudy : Round14CandidateCreatesIncludedStudy → ⊥
round14CandidateDoesNotCreateIncludedStudy ()

moreIdentityVisibilityDoesNotCreateMoreSafety :
  MoreIdentityVisibilityCreatesMoreSafety → ⊥
moreIdentityVisibilityDoesNotCreateMoreSafety ()

preferredNameFieldDoesNotCreateDownstreamNameRespect :
  PreferredNameFieldCreatesDownstreamNameRespect → ⊥
preferredNameFieldDoesNotCreateDownstreamNameRespect ()

legalNameDoesNotCreateSituatedIdentityTruth :
  LegalNameCreatesSituatedIdentityTruth → ⊥
legalNameDoesNotCreateSituatedIdentityTruth ()

onlineSettingDoesNotCreateUniversalTGDInclusion :
  OnlineSettingCreatesUniversalTGDInclusion → ⊥
onlineSettingDoesNotCreateUniversalTGDInclusion ()
