module DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as AliceChoice
import DASHI.Biology.TraumaMemoryAttractorPortfolio as TraumaMemory
import DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact as TrumpPolicy
import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek

------------------------------------------------------------------------
-- DIGITAL-ESD DISABILITY / INTERSECTIONALITY AUDIT
--
-- Source and authority discipline:
--   * disability is not collapsed into a generic equity/accessibility label;
--   * participant voice, effective accessibility and institutional support are
--     independent consumer coordinates;
--   * disability does not imply trauma, cognitive incapacity or one learning
--     style;
--   * trauma/memory, Trump-policy and Amalek lanes are structural donors only;
--     they do not create empirical disability claims or political conclusions.
------------------------------------------------------------------------

haiderDigitalAccessSource : Attr.AttributedSource
haiderDigitalAccessSource = Attr.mkDOISource
  "Md Shahrier Haider"
  "Digital technology access and usage among students with disability in Bangladeshi higher education"
  "Technology and Disability 38(3):293-301"
  "2026"
  "10.1177/10554181251403851"
  "https://doi.org/10.1177/10554181251403851"
  Attr.academicArticleSource
  "Primary qualitative multiple-case evidence from 10 purposively selected disabled university students. Supports source-bounded access/use/context claims, not population prevalence or universal technology benefit."
  Attr.publicAttribution

zhaoCoxChenGenAISource : Attr.AttributedSource
zhaoCoxChenGenAISource = Attr.mkDOISource
  "Xin Zhao; Andrew Cox; Xuanning Chen"
  "The use of generative AI by students with disabilities in higher education"
  "The Internet and Higher Education 66, 101014"
  "2025"
  "10.1016/j.iheduc.2025.101014"
  "https://doi.org/10.1016/j.iheduc.2025.101014"
  Attr.academicArticleSource
  "Primary mixed descriptive survey/content-analysis evidence from 124 valid responses by disabled higher-education students. Supports reported uses, barriers, concerns and policy-participation preferences; does not establish causal learning effects."
  Attr.publicAttribution

achtypiTELSource : Attr.AttributedSource
achtypiTELSource = Attr.mkDOISource
  "Alexia Achtypi; Abass B. Isiaka; Jeremy Schildt; Fabio Arico"
  "Technology-enhanced learning in higher education institutions: Exploring the lived experiences of students with specific learning differences and their lecturers"
  "British Educational Research Journal 52(2):864-885"
  "2026"
  "10.1002/berj.70039"
  "https://doi.org/10.1002/berj.70039"
  Attr.academicArticleSource
  "Primary qualitative interview evidence from 20 students with specific learning differences and/or autism plus 17 lecturers. Supports lived-experience and institutional-context claims, not universal TEL effectiveness."
  Attr.publicAttribution

yetergeAssistiveSustainabilitySource : Attr.AttributedSource
yetergeAssistiveSustainabilitySource = Attr.mkDOISource
  "Hulya Torun Yeterge"
  "Sustainability of assistive technology use for students with severe and multiple disabilities: a mixed methods study of teachers' attitudes and experiences"
  "Frontiers in Psychology 17:1930074"
  "2026"
  "10.3389/fpsyg.2026.1930074"
  "https://doi.org/10.3389/fpsyg.2026.1930074"
  Attr.academicArticleSource
  "Primary explanatory-sequential mixed-methods evidence: 132 special-education teachers quantitatively plus 20 qualitative interviews. Supports the separation of positive attitudes from sustainable assistive-technology use and retains institutional support, infrastructure, maintenance and training as live conditions."
  Attr.publicAttribution

roncevicRieckmannReviewSource : Attr.AttributedSource
roncevicRieckmannReviewSource = Attr.mkDOISource
  "Katarina Roncevic; Marco Rieckmann"
  "Education for Sustainable Development and Inclusive Education with particular consideration of learners with special needs: a scoping literature review"
  "Frontiers in Education 10:1593060"
  "2025"
  "10.3389/feduc.2025.1593060"
  "https://doi.org/10.3389/feduc.2025.1593060"
  Attr.academicArticleSource
  "SOTA scoping-review source. Twenty peer-reviewed articles were analysed; only nine explicitly addressed learners with special needs. The review identifies scarce empirical implementation evidence and discusses trauma-informed, culturally responsive and digital/mobile inclusion approaches. It does not substitute for primary-study evidence."
  Attr.publicAttribution

unescoDisabilityTechnologySource : Attr.AttributedSource
unescoDisabilityTechnologySource = Attr.mkNoDOISource
  "Global Education Monitoring Report Team"
  "Learners with disabilities and technology: Advocacy brief"
  "UNESCO Global Education Monitoring Report"
  "2024"
  "https://www.unesco.org/en/articles/learners-disabilities-and-technology-advocacy-brief"
  Attr.institutionalSource
  "Institutional source highlighting disability-specific technology findings and policy recommendations while keeping learners with disability and teachers central. Normative/institutional guidance does not create intervention-effect evidence."
  Attr.publicAttribution

primaryEmpiricalSources : List Attr.AttributedSource
primaryEmpiricalSources =
  haiderDigitalAccessSource
  ∷ zhaoCoxChenGenAISource
  ∷ achtypiTELSource
  ∷ yetergeAssistiveSustainabilitySource
  ∷ []

primaryEmpiricalSourceCount : Nat
primaryEmpiricalSourceCount = 4

canonicalDisabilityDigitalESDSourceAtlas : Attr.AttributedSourceAtlas
canonicalDisabilityDigitalESDSourceAtlas = Attr.mkSourceAtlas
  "digital ESD disability / intersectionality source atlas"
  "DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact"
  ( haiderDigitalAccessSource
  ∷ zhaoCoxChenGenAISource
  ∷ achtypiTELSource
  ∷ yetergeAssistiveSustainabilitySource
  ∷ roncevicRieckmannReviewSource
  ∷ unescoDisabilityTechnologySource
  ∷ [] )
  "Primary disability-specific digital-education evidence plus one SOTA inclusion-oriented ESD review and one institutional policy source. Source roles remain distinct; review/institutional context cannot backfill missing primary-study measurements."

------------------------------------------------------------------------
-- Disability-specific consumer coordinates.
------------------------------------------------------------------------

data DisabilityAuditCoordinate : Set where
  disabilitySpecificBarrierCoordinate : DisabilityAuditCoordinate
  effectiveAccessibilityCoordinate : DisabilityAuditCoordinate
  assistiveTechnologyDependencyCoordinate : DisabilityAuditCoordinate
  accessibilityAdaptationCoordinate : DisabilityAuditCoordinate
  participantVoiceCoordinate : DisabilityAuditCoordinate
  policyVoiceCoordinate : DisabilityAuditCoordinate
  disclosureVisibilityCoordinate : DisabilityAuditCoordinate
  affordabilityCoordinate : DisabilityAuditCoordinate
  maintenanceRepairContinuityCoordinate : DisabilityAuditCoordinate
  institutionalSupportCoordinate : DisabilityAuditCoordinate

disabilityAuditCoordinates : List DisabilityAuditCoordinate
disabilityAuditCoordinates =
  disabilitySpecificBarrierCoordinate
  ∷ effectiveAccessibilityCoordinate
  ∷ assistiveTechnologyDependencyCoordinate
  ∷ accessibilityAdaptationCoordinate
  ∷ participantVoiceCoordinate
  ∷ policyVoiceCoordinate
  ∷ disclosureVisibilityCoordinate
  ∷ affordabilityCoordinate
  ∷ maintenanceRepairContinuityCoordinate
  ∷ institutionalSupportCoordinate
  ∷ []

disabilityAuditCoordinateCount : Nat
disabilityAuditCoordinateCount = 10

------------------------------------------------------------------------
-- Constructive collision: broad equity/inclusion labelling cannot determine
-- whether the disability-specific consumer is actually paid.
------------------------------------------------------------------------

data DisabilityWorld : Set where
  broadEquityAccessible : DisabilityWorld
  broadEquityBarrierRetained : DisabilityWorld

broadEquityProjection : DisabilityWorld → Bool
broadEquityProjection broadEquityAccessible = true
broadEquityProjection broadEquityBarrierRetained = true

disabilityConsumerAdequate : DisabilityWorld → Bool
disabilityConsumerAdequate broadEquityAccessible = true
disabilityConsumerAdequate broadEquityBarrierRetained = false

disabilityOutcomesDiffer :
  disabilityConsumerAdequate broadEquityAccessible ≡
  disabilityConsumerAdequate broadEquityBarrierRetained → ⊥
disabilityOutcomesDiffer ()

broadEquityDisabilityCollision :
  Intersectional.NonFactorabilityWitness
    broadEquityProjection disabilityConsumerAdequate
broadEquityDisabilityCollision =
  Intersectional.nonFactorabilityWitness
    broadEquityAccessible
    broadEquityBarrierRetained
    refl
    disabilityOutcomesDiffer

broadEquityCannotDetermineDisabilityConsumer :
  Intersectional.FactorsThrough
    broadEquityProjection disabilityConsumerAdequate → ⊥
broadEquityCannotDetermineDisabilityConsumer =
  Intersectional.witnessRulesOutEveryFlatFactorisation
    broadEquityDisabilityCollision

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data BroadEquityCreatesDisabilityConsumerAdequacy : Set where
data TraumaMemoryCreatesDisabilityInference : Set where
data DisabilityCreatesTraumaInference : Set where
data PoliticalCaseCreatesDisabilityEvidence : Set where
data AmalekAnalogyCreatesDisabilityEvidence : Set where
data DisabilityCreatesCognitiveIncapacityInference : Set where
data AssistiveTechnologyUseCreatesLearningEffect : Set where

broadEquityDoesNotCreateDisabilityConsumerAdequacy :
  BroadEquityCreatesDisabilityConsumerAdequacy → ⊥
broadEquityDoesNotCreateDisabilityConsumerAdequacy ()

traumaMemoryDoesNotCreateDisabilityInference :
  TraumaMemoryCreatesDisabilityInference → ⊥
traumaMemoryDoesNotCreateDisabilityInference ()

disabilityDoesNotCreateTraumaInference :
  DisabilityCreatesTraumaInference → ⊥
disabilityDoesNotCreateTraumaInference ()

politicalCaseDoesNotCreateDisabilityEvidence :
  PoliticalCaseCreatesDisabilityEvidence → ⊥
politicalCaseDoesNotCreateDisabilityEvidence ()

amalekAnalogyDoesNotCreateDisabilityEvidence :
  AmalekAnalogyCreatesDisabilityEvidence → ⊥
amalekAnalogyDoesNotCreateDisabilityEvidence ()

disabilityDoesNotCreateCognitiveIncapacityInference :
  DisabilityCreatesCognitiveIncapacityInference → ⊥
disabilityDoesNotCreateCognitiveIncapacityInference ()

assistiveTechnologyUseDoesNotCreateLearningEffect :
  AssistiveTechnologyUseCreatesLearningEffect → ⊥
assistiveTechnologyUseDoesNotCreateLearningEffect ()

------------------------------------------------------------------------
-- Canonical repo donors retained with their authority limits.
------------------------------------------------------------------------

aliceChoiceBoundary : AliceChoice.AliceInstitutionalChoiceBoundary
aliceChoiceBoundary = AliceChoice.canonicalAliceInstitutionalChoiceBoundary

intersectionalWitness :
  Intersectional.NonFactorabilityWitness
    Intersectional.flatProjection Intersectional.relationalOutcome
intersectionalWitness = Intersectional.canonicalIntersectionalNonFactorability

amalekBoundary : Amalek.AmalekBoundary
amalekBoundary = Amalek.canonicalAmalekBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DisabilityDigitalESDBoundary : Set where
  constructor disabilityDigitalESDBoundary
  field
    disabilitySpecificPrimaryEvidenceRetained : Bool
    disabilitySpecificPrimaryEvidenceRetainedIsTrue :
      disabilitySpecificPrimaryEvidenceRetained ≡ true
    participationAndAccessibilityRemainDistinct : Bool
    participationAndAccessibilityRemainDistinctIsTrue :
      participationAndAccessibilityRemainDistinct ≡ true
    assistiveTechnologySustainabilityRetained : Bool
    assistiveTechnologySustainabilityRetainedIsTrue :
      assistiveTechnologySustainabilityRetained ≡ true
    intersectionalityRequiresRicherObserverWhenCollisionExists : Bool
    intersectionalityRequiresRicherObserverWhenCollisionExistsIsTrue :
      intersectionalityRequiresRicherObserverWhenCollisionExists ≡ true
    broadEquityLabelIsDisabilityConsumerAdequate : Bool
    broadEquityLabelIsDisabilityConsumerAdequateIsFalse :
      broadEquityLabelIsDisabilityConsumerAdequate ≡ false
    disabilityImpliesTrauma : Bool
    disabilityImpliesTraumaIsFalse : disabilityImpliesTrauma ≡ false
    traumaImpliesDisability : Bool
    traumaImpliesDisabilityIsFalse : traumaImpliesDisability ≡ false
    politicalOrReligiousAnalogyCreatesDisabilityEvidence : Bool
    politicalOrReligiousAnalogyCreatesDisabilityEvidenceIsFalse :
      politicalOrReligiousAnalogyCreatesDisabilityEvidence ≡ false
    disabilityAutomaticallyCreatesLearningDeficit : Bool
    disabilityAutomaticallyCreatesLearningDeficitIsFalse :
      disabilityAutomaticallyCreatesLearningDeficit ≡ false
    reviewOrInstitutionalSourceBackfillsPrimaryMeasurement : Bool
    reviewOrInstitutionalSourceBackfillsPrimaryMeasurementIsFalse :
      reviewOrInstitutionalSourceBackfillsPrimaryMeasurement ≡ false

open DisabilityDigitalESDBoundary public

canonicalDisabilityDigitalESDBoundary : DisabilityDigitalESDBoundary
canonicalDisabilityDigitalESDBoundary = disabilityDigitalESDBoundary
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl

disabilityDigitalESDReading : String
disabilityDigitalESDReading =
  "Disability is a consumer-distinguishing digital-ESD coordinate family, not a synonym for broad equity. Exact disability-specific primary studies show that access, assistive-technology dependency, affordability, institutional support, maintenance/repair continuity, participant voice and policy voice can remain live even when generic inclusion is asserted. Intersectionality is used only where a concrete collision shows the coarse observer inadequate. Trauma/memory/learning, Trump-policy and Amalek carriers contribute structural firewalls only and create no disability diagnosis, disability fact or political conclusion."
