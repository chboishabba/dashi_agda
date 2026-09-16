module DASHI.Education.DigitalESDCurrentScholarlySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact as PriorMap

------------------------------------------------------------------------
-- CURRENT SCHOLARLY SNOWBALL EXTENSION
------------------------------------------------------------------------

ardilaDigitalFuturesSource : Attr.AttributedSource
ardilaDigitalFuturesSource = Attr.mkDOISource
  "Maria Paula Ardila Echeverry; Andrea Gauthier; Heidi Hartikainen; Asimina Vasalou"
  "Designing for Digital Education Futures: Design Thinking for Fostering Higher Education Students' Sustainability Competencies"
  "Sustainability 17(10), 4289"
  "2025"
  "10.3390/su17104289"
  "https://doi.org/10.3390/su17104289"
  Attr.academicArticleSource
  "Reflective case study of two higher-education student teams (n=10) in a postgraduate Education and Technology module co-designing digital educational technologies for sustainability challenges. Supports source-bounded mechanisms/practices for sustainability competencies and co-design; does not establish universal learning effects, infrastructure sustainability, or participant authority beyond the studied context."
  Attr.publicAttribution

gousetiPlatformisationSource : Attr.AttributedSource
gousetiPlatformisationSource = Attr.mkDOISource
  "Anastasia Gouseti; Patricia Shaw"
  "When platformisation meets schooling: exploring teachers, students and parents' experiences of digital platform use"
  "Learning, Media and Technology"
  "2026"
  "10.1080/17439884.2026.2653746"
  "https://doi.org/10.1080/17439884.2026.2653746"
  Attr.academicArticleSource
  "Qualitative study of school leaders, teachers, students and parents in two English secondary schools. Supports context-bounded platformisation effects including streamlining, monitoring/surveillance, digital exclusion and teacher digital wellbeing; does not prove universal platform effects or sustainability outcomes."
  Attr.publicAttribution

zagamiAustralianEdtechSource : Attr.AttributedSource
zagamiAustralianEdtechSource = Attr.mkDOISource
  "Jason Zagami"
  "Beyond the hype: success, collapse, and the making of edtech in Australia"
  "Learning, Media and Technology"
  "2026"
  "10.1080/17439884.2026.2683480"
  "https://doi.org/10.1080/17439884.2026.2683480"
  Attr.academicArticleSource
  "Comparative Australian edtech case study using public-document analysis and temporal mapping across Canva for Education, Education Perfect, LearningField and Grok Academy. Supports context-bounded governance, funding, legitimacy and durability dynamics; it does not establish a universal rule for platform success, interoperability or sustainability."
  Attr.publicAttribution

chughSustainabilityParadoxSource : Attr.AttributedSource
chughSustainabilityParadoxSource = Attr.mkDOISource
  "Ritesh Chugh"
  "The sustainability paradox: rethinking digital technologies in education for a sustainable future"
  "Humanities and Social Sciences Communications 13, 275"
  "2026"
  "10.1057/s41599-026-06845-5"
  "https://doi.org/10.1057/s41599-026-06845-5"
  Attr.academicArticleSource
  "Opinion paper framing digital education as a sustainability paradox across environmental and social dimensions, with lifecycle-oriented attention to energy, devices, data infrastructure, equity, procurement and circular-economy strategies. It is a close conceptual antecedent for the reverse-direction sustainability claim and must be cited as such; it does not supply empirical intervention effects or the manuscript's reciprocal ESD-capacity/payment/participant-authority machinery."
  Attr.publicAttribution

holstSDG47MonitoringSource : Attr.AttributedSource
holstSDG47MonitoringSource = Attr.mkDOISource
  "Jorrit Holst; Mandy Singer-Brodowski; Antje Brock; Gerhard de Haan"
  "Monitoring SDG 4.7: Assessing Education for Sustainable Development in policies, curricula, training of educators and student assessment (input-indicator)"
  "Sustainable Development 32(4), 3908-3923"
  "2024"
  "10.1002/sd.2865"
  "https://doi.org/10.1002/sd.2865"
  Attr.academicArticleSource
  "Longitudinal input-level ESD monitoring study and methodology using more than 11,000 documents across ten years and all formal education sectors in Germany. Supports independent assessment of depth and speed of ESD integration in policies, curricula, educator training and student assessment; input integration does not by itself establish learning, output/outcome transformation or digital-ESD effects."
  Attr.publicAttribution

canonicalCurrentScholarlySourceAtlas : Attr.AttributedSourceAtlas
canonicalCurrentScholarlySourceAtlas = Attr.mkSourceAtlas
  "current digital-ESD scholarly snowball extension"
  "DASHI.Education.DigitalESDCurrentScholarlySnowballExact"
  ( ardilaDigitalFuturesSource
  ∷ gousetiPlatformisationSource
  ∷ zagamiAustralianEdtechSource
  ∷ chughSustainabilityParadoxSource
  ∷ holstSDG47MonitoringSource
  ∷ [] )
  "Recent scholarly candidates extending the existing digital-ESD literature map with higher-education sustainability co-design, school platformisation experience, Australian edtech governance/durability cases, a close sustainability-paradox conceptual antecedent, and longitudinal SDG 4.7 input-monitoring methodology. Acquisition remains candidate-only pending structured search and screening."

ardilaSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt ardilaDigitalFuturesSource
ardilaSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt ardilaDigitalFuturesSource

gousetiSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt gousetiPlatformisationSource
gousetiSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt gousetiPlatformisationSource

zagamiSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt zagamiAustralianEdtechSource
zagamiSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt zagamiAustralianEdtechSource

chughSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt chughSustainabilityParadoxSource
chughSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt chughSustainabilityParadoxSource

holstSourceRoleReceipt : Snowball.SourceRoleSnowballReceipt holstSDG47MonitoringSource
holstSourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt holstSDG47MonitoringSource

priorLiteratureMapRetained : PriorMap.DigitalESDLiteratureMap
priorLiteratureMapRetained = PriorMap.canonicalDigitalESDLiteratureMap

data SingleCaseCreatesUniversalDigitalESDRule : Set where
data TwoSchoolPlatformStudyCreatesUniversalPlatformEffect : Set where
data AustralianEdtechCaseCreatesUniversalDurabilityRule : Set where
data OpinionPaperCreatesEmpiricalDigitalESDEffect : Set where
data SustainabilityParadoxExhaustsReciprocalDigitalESDFramework : Set where
data InputIndicatorMonitoringCreatesOutcomeTransformation : Set where

singleCaseDoesNotCreateUniversalDigitalESDRule : SingleCaseCreatesUniversalDigitalESDRule → ⊥
singleCaseDoesNotCreateUniversalDigitalESDRule ()

twoSchoolPlatformStudyDoesNotCreateUniversalPlatformEffect : TwoSchoolPlatformStudyCreatesUniversalPlatformEffect → ⊥
twoSchoolPlatformStudyDoesNotCreateUniversalPlatformEffect ()

australianEdtechCaseDoesNotCreateUniversalDurabilityRule : AustralianEdtechCaseCreatesUniversalDurabilityRule → ⊥
australianEdtechCaseDoesNotCreateUniversalDurabilityRule ()

opinionPaperDoesNotCreateEmpiricalDigitalESDEffect : OpinionPaperCreatesEmpiricalDigitalESDEffect → ⊥
opinionPaperDoesNotCreateEmpiricalDigitalESDEffect ()

sustainabilityParadoxDoesNotExhaustReciprocalDigitalESDFramework : SustainabilityParadoxExhaustsReciprocalDigitalESDFramework → ⊥
sustainabilityParadoxDoesNotExhaustReciprocalDigitalESDFramework ()

inputIndicatorMonitoringDoesNotCreateOutcomeTransformation : InputIndicatorMonitoringCreatesOutcomeTransformation → ⊥
inputIndicatorMonitoringDoesNotCreateOutcomeTransformation ()

record ScholarlyCandidateBoundary : Set where
  constructor scholarly-candidate-boundary
  field
    ardilaSourceRolePaid : Bool
    ardilaSourceRolePaidIsTrue : ardilaSourceRolePaid ≡ true
    gousetiSourceRolePaid : Bool
    gousetiSourceRolePaidIsTrue : gousetiSourceRolePaid ≡ true
    zagamiSourceRolePaid : Bool
    zagamiSourceRolePaidIsTrue : zagamiSourceRolePaid ≡ true
    chughSourceRolePaid : Bool
    chughSourceRolePaidIsTrue : chughSourceRolePaid ≡ true
    holstSourceRolePaid : Bool
    holstSourceRolePaidIsTrue : holstSourceRolePaid ≡ true
    acquisitionCreatesInclusion : Bool
    acquisitionCreatesInclusionIsFalse : acquisitionCreatesInclusion ≡ false
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open ScholarlyCandidateBoundary public

canonicalScholarlyCandidateBoundary : ScholarlyCandidateBoundary
canonicalScholarlyCandidateBoundary = scholarly-candidate-boundary
  true refl true refl true refl true refl true refl false refl false refl false refl
