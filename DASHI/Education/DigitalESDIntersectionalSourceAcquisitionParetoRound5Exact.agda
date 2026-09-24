module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound5Exact where

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
-- ROUND 5: PHILOSOPHY-SEEDED, EMPIRICALLY PAID SURVEILLANCE/POWER RESIDUALS.
--
-- Philosophy is used here only to seed discriminating questions. Empirical
-- papers own their observations. Foucault/anti-panopticon/critical-platform
-- lenses do not become population laws, causal effects, or study authorship.
------------------------------------------------------------------------

data Round5Residual : Set where
  aiSurveillanceByPluralStakeholderSubjectification : Round5Residual
  privacyByAfricanSituatedContext : Round5Residual
  platformGovernanceByCommercialTechnicalEducationalPower : Round5Residual
  learningAnalyticsPrivacyByCrossCulturalStudentVariation : Round5Residual
  transparencyInterventionByStudentAwareness : Round5Residual

record Round5Candidate : Set where
  constructor round5-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : Round5Residual
    auditLens : PhilosophyAudit.PhilosophyAuditFamily
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round5Candidate public

mkRound5Candidate :
  (source : Attr.AttributedSource) →
  Round5Residual →
  PhilosophyAudit.PhilosophyAuditFamily →
  String →
  String →
  Round5Candidate
mkRound5Candidate source residual audit reading limitation =
  round5-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound5Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 5"))
    "Dewey classification unresolved; no nearest-label substitution"
    residual
    audit
    reading
    limitation
    false refl

------------------------------------------------------------------------
-- AI surveillance / Foucauldian analytic frame with empirical stakeholders.
------------------------------------------------------------------------

daiThomasRawolleSource : Attr.AttributedSource
daiThomasRawolleSource = Attr.mkDOISource
  "Ruixun Dai; Matthew Krehl Edward Thomas; Shaun Rawolle"
  "Revisiting Foucault's panopticon: how does AI surveillance transform educational norms?"
  "British Journal of Sociology of Education 46(5), 650-668"
  "2025"
  "10.1080/01425692.2025.2501118"
  "https://doi.org/10.1080/01425692.2025.2501118"
  Attr.academicArticleSource
  "Qualitative study using Foucauldian surveillance/disciplinary-power concepts to interpret responses from 27 English- and Chinese-speaking stakeholders including students, teachers, administrators and parents about AI-mediated educational surveillance and emergent norms."
  Attr.publicAttribution

daiCandidate : Round5Candidate
daiCandidate = mkRound5Candidate
  daiThomasRawolleSource
  aiSurveillanceByPluralStakeholderSubjectification
  PhilosophyAudit.foucaultSubjectificationDisciplinePower
  "High-alpha bridge between an explicitly Foucauldian analytic frame and empirical plural-stakeholder observations about AI surveillance, behaviour and norms. The empirical observations remain owned by Dai/Thomas/Rawolle; Foucault supplies only the interpretive source lineage."
  "Small qualitative stakeholder sample without geographical restriction; does not establish universal AI-surveillance effects, marginalized-group incidence, causal transformation, or whole-Foucault doctrine."

------------------------------------------------------------------------
-- Privacy concepts situated in African higher education.
------------------------------------------------------------------------

prinslooKaliisaSource : Attr.AttributedSource
prinslooKaliisaSource = Attr.mkDOISource
  "Paul Prinsloo; Rogers Kaliisa"
  "Dimensions of privacy and its implications for learning analytics. Preliminary insights from/for African higher education"
  "Learning, Media and Technology 50(4), 432-447"
  "2024 online / 2025 issue"
  "10.1080/17439884.2024.2321437"
  "https://doi.org/10.1080/17439884.2024.2321437"
  Attr.academicArticleSource
  "Phenomenological interpretive study drawing on 13 African higher-education experts; examines privacy in learning analytics in relation to colonial history, culture, religion, education and individual/communal understandings, challenging unqualified Global-North universality."
  Attr.publicAttribution

prinslooCandidate : Round5Candidate
prinslooCandidate = mkRound5Candidate
  prinslooKaliisaSource
  privacyByAfricanSituatedContext
  PhilosophyAudit.philosophyClaimProvenancePromotion
  "Direct candidate for situated-observer/privacy x colonial-history/culture/context fibres and for testing whether a supposedly universal privacy construct factors through one institutional or Global-North observer."
  "Expert perspectives are not direct student testimony and do not establish one pan-African privacy essence, prevalence estimate, legal rule or educational effect."

------------------------------------------------------------------------
-- Platform governance / ownership and intermediary power.
------------------------------------------------------------------------

nicholsDixonRomanSource : Attr.AttributedSource
nicholsDixonRomanSource = Attr.mkDOISource
  "T. Philip Nichols; Ezekiel Dixon-Román"
  "Platform Governance and Education Policy: Power and Politics in Emerging Edtech Ecologies"
  "Educational Evaluation and Policy Analysis 46(2)"
  "2024"
  "10.3102/01623737231202469"
  "https://doi.org/10.3102/01623737231202469"
  Attr.academicArticleSource
  "Critical policy/platform-studies article analysing platform technologies and their owners as intermediaries brokering commercial, technical and educational relations, with explicit questions about policy power and educational equity."
  Attr.publicAttribution

nicholsCandidate : Round5Candidate
nicholsCandidate = mkRound5Candidate
  nicholsDixonRomanSource
  platformGovernanceByCommercialTechnicalEducationalPower
  PhilosophyAudit.platformInstitutionalPower
  "High-alpha political-economy/platform-power donor for ownership/intermediation x governance x equity. It sharpens the current vendor-power residual beyond privacy compliance alone."
  "Analytical/policy framework; platform intermediation does not by itself prove domination, surveillance harm, learning effect or participant-authority loss in a named deployment."

------------------------------------------------------------------------
-- Cross-cultural variation in student privacy concerns.
------------------------------------------------------------------------

vibergEtAlSource : Attr.AttributedSource
vibergEtAlSource = Attr.mkDOISource
  "Olga Viberg; René F. Kizilcec; Ioana Jivet; Alejandra Martínez Monés; Alice Oh; Chantal Mutimukwe; Stefan Hrastinski; Maren Scheffel"
  "Cultural differences in students' privacy concerns in learning analytics across Germany, South Korea, Spain, Sweden, and the United States"
  "Computers in Human Behavior Reports 14, 100416"
  "2024"
  "10.1016/j.chbr.2024.100416"
  "https://doi.org/10.1016/j.chbr.2024.100416"
  Attr.academicArticleSource
  "Survey of 762 university students across five countries measuring privacy risk, control, concerns, trust and non-self-disclosure alongside cultural values; reports cross-country/context variation rather than one invariant privacy response."
  Attr.publicAttribution

vibergCandidate : Round5Candidate
vibergCandidate = mkRound5Candidate
  vibergEtAlSource
  learningAnalyticsPrivacyByCrossCulturalStudentVariation
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Direct participant-observer source for privacy/control/trust x cultural/context variation. Useful against any source-audit projection that treats institutional data visibility or one-country student preference as globally representative."
  "Five-country higher-education survey; cultural-value associations do not create deterministic national essences, causal surveillance effects, disability incidence or universal consent rules."

------------------------------------------------------------------------
-- Transparency intervention: awareness rather than assumed consent.
------------------------------------------------------------------------

seppTransparencySource : Attr.AttributedSource
seppTransparencySource = Attr.mkDOISource
  "Stoo Sepp"
  "Towards More Transparency in Learning Analytics: Sharing Information with University Students Increases their Awareness of Data Collection Practices"
  "Journal of Learning Analytics"
  "2025"
  "10.18608/jla.2025.8713"
  "https://doi.org/10.18608/jla.2025.8713"
  Attr.academicArticleSource
  "Higher-education study testing alternative data-disclosure statement formats as a practical transparency intervention for student awareness of learning-analytics data collection practices."
  Attr.publicAttribution

seppCandidate : Round5Candidate
seppCandidate = mkRound5Candidate
  seppTransparencySource
  transparencyInterventionByStudentAwareness
  PhilosophyAudit.antiPanopticonVisibilityAuthority
  "Useful positive intervention candidate: inspectable disclosure/provenance can be tested against student awareness rather than assumed from policy existence. This complements anti-panopticon evidence-path requirements with an empirical awareness outcome."
  "Awareness improvement is not informed consent, participant decision authority, privacy protection, trust, behavioural effect or long-term governance durability."

canonicalRound5Frontier : List Round5Candidate
canonicalRound5Frontier =
  daiCandidate
  ∷ prinslooCandidate
  ∷ nicholsCandidate
  ∷ vibergCandidate
  ∷ seppCandidate
  ∷ []

------------------------------------------------------------------------
-- No-promotion / observer firewalls.
------------------------------------------------------------------------

data Round5CandidateCreatesIncludedStudy : Set where
data FoucaultFrameCreatesEmpiricalOwnership : Set where
data PhilosophicalAuditCreatesStudyFinding : Set where
data PlatformPowerFrameworkCreatesObservedStudentHarm : Set where
data CrossCulturalVariationCreatesUniversalPrivacyLaw : Set where
data TransparencyCreatesConsentOrAuthority : Set where

round5CandidateDoesNotCreateIncludedStudy : Round5CandidateCreatesIncludedStudy → ⊥
round5CandidateDoesNotCreateIncludedStudy ()

foucaultFrameDoesNotCreateEmpiricalOwnership :
  FoucaultFrameCreatesEmpiricalOwnership → ⊥
foucaultFrameDoesNotCreateEmpiricalOwnership ()

philosophicalAuditDoesNotCreateStudyFinding :
  PhilosophicalAuditCreatesStudyFinding → ⊥
philosophicalAuditDoesNotCreateStudyFinding ()

platformPowerFrameworkDoesNotCreateObservedStudentHarm :
  PlatformPowerFrameworkCreatesObservedStudentHarm → ⊥
platformPowerFrameworkDoesNotCreateObservedStudentHarm ()

crossCulturalVariationDoesNotCreateUniversalPrivacyLaw :
  CrossCulturalVariationCreatesUniversalPrivacyLaw → ⊥
crossCulturalVariationDoesNotCreateUniversalPrivacyLaw ()

transparencyDoesNotCreateConsentOrAuthority :
  TransparencyCreatesConsentOrAuthority → ⊥
transparencyDoesNotCreateConsentOrAuthority ()
