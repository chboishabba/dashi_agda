module DASHI.Education.DigitalESDNormativeStandardsAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- VERSIONED NORMATIVE / PROCESS LENSES
--
-- Public catalogue identities and public-scope descriptions only. ISO text is
-- copyrighted and is not reproduced here. Standards/frameworks constrain or
-- organise a process surface; they do not create educational-effect evidence.
------------------------------------------------------------------------

data StandardRelationship : Set where
  addresses : StandardRelationship
  operationalises : StandardRelationship
  evaluatesAgainst : StandardRelationship
  claimsConformity : StandardRelationship
  certifiedConformity : StandardRelationship
  notApplicable : StandardRelationship

record StandardLens : Set where
  constructor standard-lens
  field
    source : Attr.AttributedSource
    standardIdentifier : String
    editionOrVersion : String
    publicScopeReading : String
    qidDemand : Identity.ExternalIdentityDemand
    deweyClassificationState : String
    defaultRelationship : StandardRelationship

open StandardLens public

mkTechnicalStandardLens :
  String → String → String → String → String → String → String →
  StandardLens
mkTechnicalStandardLens organisation identifier edition title url scope dewey =
  standard-lens
    (Attr.mkNoDOISource
      organisation
      title
      identifier
      edition
      url
      Attr.technicalStandardSource
      scope
      Attr.publicAttribution)
    identifier
    edition
    scope
    (Identity.mkOptionalIdentityDemand
      "DigitalESDNormativeStandardsAtlasExact"
      identifier
      title
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object QID recorded by this atlas"))
    dewey
    addresses

mkFrameworkLens :
  Attr.AttributedSource → String → String → String → String → StandardLens
mkFrameworkLens src identifier version scope dewey =
  standard-lens
    src identifier version scope
    (Identity.mkOptionalIdentityDemand
      "DigitalESDNormativeStandardsAtlasExact"
      identifier
      (Attr.sourceTitle src)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object QID recorded by this atlas"))
    dewey
    addresses

iso9001_2026 : StandardLens
iso9001_2026 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 9001:2026"
  "2026"
  "Quality management systems — Requirements"
  "https://www.iso.org/standard/9001.html"
  "Public ISO catalogue scope: requirements for establishing, implementing, maintaining and continually improving a quality management system. Does not establish educational effectiveness or sustainability outcomes."
  "unresolved/not assigned by this atlas"

isoIEC42001_2023 : StandardLens
isoIEC42001_2023 = mkTechnicalStandardLens
  "ISO/IEC"
  "ISO/IEC 42001:2023"
  "2023"
  "Information technology — Artificial intelligence — Management system"
  "https://www.iso.org/standard/81230.html"
  "AI management-system lens for organisational governance, planning, operation, evaluation and improvement; not pedagogical-effect evidence."
  "unresolved/not assigned by this atlas"

isoIEC27001_2022 : StandardLens
isoIEC27001_2022 = mkTechnicalStandardLens
  "ISO/IEC"
  "ISO/IEC 27001:2022"
  "2022"
  "Information security, cybersecurity and privacy protection — Information security management systems — Requirements"
  "https://www.iso.org/standard/27001.html"
  "Information-security management-system lens; confidentiality/integrity/availability management does not imply accessibility, participant authority or educational benefit."
  "unresolved/not assigned by this atlas"

isoIEC27701_2025 : StandardLens
isoIEC27701_2025 = mkTechnicalStandardLens
  "ISO/IEC"
  "ISO/IEC 27701:2025"
  "2025"
  "Information security, cybersecurity and privacy protection — Privacy information management systems — Requirements and guidance"
  "https://www.iso.org/standard/27701.html"
  "Privacy-information-management lens; privacy management does not manufacture consent, epistemic agency, or justified retention."
  "unresolved/not assigned by this atlas"

isoIEC23894_2023 : StandardLens
isoIEC23894_2023 = mkTechnicalStandardLens
  "ISO/IEC"
  "ISO/IEC 23894:2023"
  "2023"
  "Information technology — Artificial intelligence — Guidance on risk management"
  "https://www.iso.org/standard/77304.html"
  "AI risk-management guidance lens; identifies risk-process obligations but does not establish educational outcome or distributed impact."
  "unresolved/not assigned by this atlas"

iso9241_110_2020 : StandardLens
iso9241_110_2020 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 9241-110:2020"
  "2020"
  "Ergonomics of human-system interaction — Part 110: Interaction principles"
  "https://www.iso.org/standard/75258.html"
  "Interaction-principles lens; formal usability does not imply realised accessibility or effective educational participation."
  "unresolved/not assigned by this atlas"

iso9241_161_2025 : StandardLens
iso9241_161_2025 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 9241-161:2025"
  "2025"
  "Ergonomics of human-system interaction — Part 161: Visual user-interface elements"
  "https://www.iso.org/standard/85790.html"
  "Visual user-interface element design lens; does not by itself establish access for a situated learner population."
  "unresolved/not assigned by this atlas"

iso9241_210_2019 : StandardLens
iso9241_210_2019 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 9241-210:2019"
  "2019"
  "Ergonomics of human-system interaction — Part 210: Human-centred design for interactive systems"
  "https://www.iso.org/standard/77520.html"
  "Human-centred-design process lens; use of a process does not establish whose experience or authority was actually represented."
  "unresolved/not assigned by this atlas"

iso9241_306_2018 : StandardLens
iso9241_306_2018 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 9241-306:2018"
  "2018"
  "Ergonomics of human-system interaction — Part 306: Field assessment methods for electronic visual displays"
  "https://www.iso.org/standard/65063.html"
  "Electronic-display field-assessment lens; not a whole educational-accessibility or learning-effect measure."
  "unresolved/not assigned by this atlas"

iso24552_2020 : StandardLens
iso24552_2020 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 24552:2020"
  "2020"
  "Ergonomics — Accessible design — Accessibility of information presented on visual displays of small consumer products"
  "https://www.iso.org/standard/73276.html"
  "Accessible-design lens for information on small visual displays; not a universal disability-access or education-system measure."
  "unresolved/not assigned by this atlas"

iso16817_2017 : StandardLens
iso16817_2017 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 16817:2017"
  "2017"
  "Building environment design — Indoor environment — Design process for the visual environment"
  "https://www.iso.org/standard/61021.html"
  "Indoor visual-environment design lens connecting user/environment/building concerns; the physical-school baseline is not treated as impact-free."
  "unresolved/not assigned by this atlas"

iso24505_1_2025 : StandardLens
iso24505_1_2025 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 24505-1:2025"
  "2025"
  "Ergonomics — Accessible design — Part 1: Colour combinations for young and older people without visual impairments"
  "https://www.iso.org/standard/88605.html"
  "Version-pinned colour-accessibility lens; retained separately from the superseded generic ISO 24505 identity."
  "unresolved/not assigned by this atlas"

iso24505_2_2025 : StandardLens
iso24505_2_2025 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 24505-2:2025"
  "2025"
  "Ergonomics — Accessible design — Part 2: Colour combinations for people with colour deficiency and low vision"
  "https://www.iso.org/standard/88606.html"
  "Version-pinned colour-accessibility lens for colour deficiency/low-vision context; no generic accessibility promotion."
  "unresolved/not assigned by this atlas"

iso22727_2007 : StandardLens
iso22727_2007 = mkTechnicalStandardLens
  "International Organization for Standardization"
  "ISO 22727:2007"
  "2007"
  "Graphical symbols — Creation and design of public information symbols — Requirements"
  "https://www.iso.org/standard/41091.html"
  "Public-information-symbol design lens. Any successor/draft lineage is a separate identity and may not be silently substituted."
  "unresolved/not assigned by this atlas"

nistAIRMFSource : Attr.AttributedSource
nistAIRMFSource = Attr.mkDOISource
  "Elham Tabassi"
  "Artificial Intelligence Risk Management Framework (AI RMF 1.0)"
  "NIST AI 100-1"
  "2023"
  "10.6028/NIST.AI.100-1"
  "https://doi.org/10.6028/NIST.AI.100-1"
  Attr.governmentSource
  "Voluntary AI risk-management framework for organisations designing, developing, deploying or using AI. NIST states AI RMF 1.0 is under revision in 2026; this atlas therefore pins version 1.0 and does not project draft revisions backward."
  Attr.publicAttribution

nistAIRMF10 : StandardLens
nistAIRMF10 = mkFrameworkLens
  nistAIRMFSource
  "NIST AI RMF 1.0 / NIST AI 100-1"
  "1.0 (2023)"
  "Voluntary AI risk-management lens addressing risks to individuals, organisations and society; framework use does not establish realised educational outcomes or distributed risk adequacy."
  "unresolved/not assigned by this atlas"

itil4Source : Attr.AttributedSource
itil4Source = Attr.mkNoDOISource
  "PeopleCert / ITIL"
  "ITIL 4 practices"
  "ITIL 4"
  "current ITIL 4 practice family"
  "https://www.peoplecert.org/ITIL4-practices"
  Attr.practitionerSource
  "Service-management/process source used only for operational continuity, incident/problem/change/support and continual-improvement lenses. It is not empirical education evidence."
  Attr.publicAttribution

itil4 : StandardLens
itil4 = mkFrameworkLens
  itil4Source
  "ITIL 4"
  "ITIL 4"
  "Service-management lens for operational continuity and improvement; service availability does not imply effective accessibility or social provisioning continuity."
  "unresolved/not assigned by this atlas"

sixSigmaSource : Attr.AttributedSource
sixSigmaSource = Attr.mkNoDOISource
  "American Society for Quality"
  "DMAIC Process: Define, Measure, Analyze, Improve, Control"
  "ASQ quality resources"
  "current public guidance"
  "https://asq.org/quality-resources/dmaic"
  Attr.practitionerSource
  "Process-improvement methodology lens. Efficiency/process control do not by themselves establish sustainability, justice, accessibility, or absolute burden reduction."
  Attr.publicAttribution

sixSigmaDMAIC : StandardLens
sixSigmaDMAIC = mkFrameworkLens
  sixSigmaSource
  "Six Sigma / DMAIC"
  "DMAIC"
  "Measurement/improvement lens: define, measure, analyse, improve and control an existing process; not a sustainability theory or educational-effect source."
  "unresolved/not assigned by this atlas"

isoIEC42005_2025 : StandardLens
isoIEC42005_2025 = mkTechnicalStandardLens
  "ISO/IEC"
  "ISO/IEC 42005:2025"
  "2025"
  "Artificial intelligence — AI system impact assessment"
  "https://www.iso.org/standard/44545.html"
  "Adjacent AI impact-assessment lens retained as a bounded candidate for incidence/intersection consumers. Public catalogue identity/scope only; full copyrighted requirements are not reproduced."
  "unresolved/not assigned by this atlas"

canonicalStandardLenses : List StandardLens
canonicalStandardLenses =
  iso9001_2026
  ∷ isoIEC42001_2023
  ∷ isoIEC27001_2022
  ∷ isoIEC27701_2025
  ∷ isoIEC23894_2023
  ∷ iso9241_110_2020
  ∷ iso9241_161_2025
  ∷ iso9241_210_2019
  ∷ iso9241_306_2018
  ∷ iso24552_2020
  ∷ iso16817_2017
  ∷ iso24505_1_2025
  ∷ iso24505_2_2025
  ∷ iso22727_2007
  ∷ nistAIRMF10
  ∷ itil4
  ∷ sixSigmaDMAIC
  ∷ isoIEC42005_2025
  ∷ []

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data StandardMentionCreatesConformity : Set where
data ClaimedConformityCreatesCertifiedConformity : Set where
data StandardConformityCreatesEducationalEffect : Set where
data SecurityAvailabilityCreatesHumanAccessibility : Set where
data NormativeLensCreatesParticipantAuthority : Set where

standardMentionDoesNotCreateConformity : StandardMentionCreatesConformity → ⊥
standardMentionDoesNotCreateConformity ()

claimedConformityDoesNotCreateCertifiedConformity :
  ClaimedConformityCreatesCertifiedConformity → ⊥
claimedConformityDoesNotCreateCertifiedConformity ()

standardConformityDoesNotCreateEducationalEffect :
  StandardConformityCreatesEducationalEffect → ⊥
standardConformityDoesNotCreateEducationalEffect ()

securityAvailabilityDoesNotCreateHumanAccessibility :
  SecurityAvailabilityCreatesHumanAccessibility → ⊥
securityAvailabilityDoesNotCreateHumanAccessibility ()

normativeLensDoesNotCreateParticipantAuthority :
  NormativeLensCreatesParticipantAuthority → ⊥
normativeLensDoesNotCreateParticipantAuthority ()
