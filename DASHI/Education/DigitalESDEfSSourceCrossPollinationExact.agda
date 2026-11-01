module DASHI.Education.DigitalESDEfSSourceCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact as Prior
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDTilburySourceRoleExact as Tilbury

-- Supplied published sources plus direct reuse of the existing Tilbury atlas.
-- The bridges are new DASHI candidate interpretations, never paper findings.
-- No admission, independent EfS source-span review, or causal outcome is claimed.
-- Private manuscript drafts are deliberately absent from this public module.
-- All candidate claims retain the original source identity, role, and limit.

taimurOnukiSource : Attr.AttributedSource
taimurOnukiSource = Attr.mkDOISource
  "Sadaf Taimur; Motoharu Onuki"
  "Design thinking as digital transformative pedagogy in higher sustainability education: Cases from Japan and Germany"
  "International Journal of Educational Research 114, 101994"
  "2022"
  "10.1016/j.ijer.2022.101994"
  "https://doi.org/10.1016/j.ijer.2022.101994"
  Attr.academicArticleSource
  "Reported application of digital transformative pedagogy components in two cases and participant perceptions of learning conditions. BOUNDARY: No independent proof of durable personal transformation, ecological outcomes, general intervention effects or transfer to other institutions."
  Attr.publicAttribution

nilssonDahlstromSource : Attr.AttributedSource
nilssonDahlstromSource = Attr.mkDOISource
  "Åsa Nilsson Dahlström"
  "Challenges and opportunities for social sustainability in education: a scoping review"
  "Cogent Social Sciences 11(1), 2491706"
  "2025"
  "10.1080/23311886.2025.2491706"
  "https://doi.org/10.1080/23311886.2025.2491706"
  Attr.academicArticleSource
  "Documents differences and conceptual/assessment difficulties in definitions and enactment of social sustainability. BOUNDARY: The review's denominators and synthesis belong to its author; they cannot pay Digital-ESD's database, admission or outcome obligations."
  Attr.publicAttribution

adefilaEcoCOILSource : Attr.AttributedSource
adefilaEcoCOILSource = Attr.mkDOISource
  "Arinola Adefila; Osman Arrobbio; Geraldine Brown; Zoe Robinson; Gary Spolander; Ilkhom Soliev; Bret Willers; Luca Morini; Dario Padovan; Katherine Wimpenny"
  "Ecologized Collaborative Online International Learning: Tackling Wicked Sustainability Problems Through Education for Sustainable Development"
  "Journal of Teacher Education for Sustainability 23(1), 41-57"
  "2021"
  "10.2478/jtes-2021-0004"
  "https://doi.org/10.2478/jtes-2021-0004"
  Attr.academicArticleSource
  "Models participatory co-creation, intercultural participation, coalition building and sustainability problem inquiry in digital settings. BOUNDARY: Conceptual/model claims are not independent measurement of community authority, collective impacts or ecological outcomes."
  Attr.publicAttribution

singhCommunitySource : Attr.AttributedSource
singhCommunitySource = Attr.mkDOISource
  "Wafa Singh; Raisuyah Bhagwan; Manju Singh"
  "Leveraging community-engaged teaching and learning in higher education institutions for advancing sustainable development: a literature review"
  "International Journal of Sustainability in Higher Education 27(1), 114-131"
  "2026"
  "10.1108/IJSHE-01-2024-0066"
  "https://doi.org/10.1108/IJSHE-01-2024-0066"
  Attr.academicArticleSource
  "Reviews pedagogical arrangements, community partnerships, sustainability competencies and conditions that constrain enactment. BOUNDARY: Review-level reports do not demonstrate causal effects of a specific digital intervention or authorise a university to speak for community partners."
  Attr.publicAttribution

barthCompetenciesSource : Attr.AttributedSource
barthCompetenciesSource = Attr.mkDOISource
  "Matthias Barth; Jasmin Godemann; Marco Rieckmann; Ute Stoltenberg"
  "Developing key competencies for sustainable development in higher education"
  "International Journal of Sustainability in Higher Education 8(4), 416-430"
  "2007"
  "10.1108/14676370710823582"
  "https://doi.org/10.1108/14676370710823582"
  Attr.academicArticleSource
  "Identifies roles for cognitive and non-cognitive dispositions, multiple learning contexts and student responsibility in competence development. BOUNDARY: Original authors identify remaining uncertainty about interdependencies; no digital intervention comparison or universal causal mechanism."
  Attr.publicAttribution

giridharanCompetenciesSource : Attr.AttributedSource
giridharanCompetenciesSource = Attr.mkNoDOISource
  "Beena Giridharan"
  "Learning for a Sustainable Future: Developing Key Competencies"
  "Introduction to Sustainable Development Leadership and Strategies in Higher Education, chapter 8, Emerald, pp. 155-166"
  "2020"
  "https://ebookcentral.proquest.com/lib/usq/detail.action?docID=6238640"
  Attr.academicChapterSource
  "Develops a strategic account of future-facing competencies, flexible learning, digital provision and changing institutional models. BOUNDARY: Conceptual and policy-facing discussion does not supply measured evidence of sustainability competence, durability or employment benefit."
  Attr.publicAttribution

jepsenCookeAccessibilitySource : Attr.AttributedSource
jepsenCookeAccessibilitySource = Attr.mkNoDOISource
  "Thomas F. Jepsen; Theo Cooke"
  "Intentional Inclusion in HigherEd E-Learning: Embedding Universal Accessibility Through Digital Technology"
  "2nd Global Trends in E-learning Forum, pp. 61-65; SSRN 4320172"
  "2023"
  "https://ssrn.com/abstract=4320172"
  Attr.practitionerSource
  "Argues that design must accommodate conflicting access needs and context-specific learner constraints. BOUNDARY: Industry perspective and advocated outcomes do not establish audited disability accessibility, retention effects or causal employment outcomes."
  Attr.publicAttribution

ferreiraRyanTilburySource : Attr.AttributedSource
ferreiraRyanTilburySource = Attr.mkDOISource
  "Jo-Anne Ferreira; Lisa Ryan; Daniella Tilbury"
  "Mainstreaming education for sustainable development in initial teacher education in Australia: a review of existing professional development models"
  "Journal of Education for Teaching 33(2), 225-239"
  "2007"
  "10.1080/02607470701259515"
  "https://doi.org/10.1080/02607470701259515"
  Attr.academicArticleSource
  "Separates resource delivery, professional learning and more systemic change approaches in teacher education. BOUNDARY: Initial teacher education context and professional-development models do not independently establish effects in digital university teaching."
  Attr.publicAttribution

ferreiraRyanSystemSource : Attr.AttributedSource
ferreiraRyanSystemSource = Attr.mkDOISource
  "Jo-Anne Ferreira; Lisa Ryan"
  "Working the System: A Model for System-Wide Change in Pre-Service Teacher Education"
  "Australian Journal of Teacher Education 37(12)"
  "2013"
  "10.14221/ajte.2012v37n12.3"
  "https://doi.org/10.14221/ajte.2012v37n12.3"
  Attr.academicArticleSource
  "Studies organisational curriculum change and proposes an integrated Mainstreaming Change model across system levels. BOUNDARY: Proposed systems model is not proof of general digital-ESD or longitudinal intervention outcomes."
  Attr.publicAttribution

ferreiraRyanDavisSource : Attr.AttributedSource
ferreiraRyanDavisSource = Attr.mkDOISource
  "Jo-Anne Ferreira; Lisa Ryan; Julie Davis"
  "Developing Knowledge and Leadership in Pre-Service Teacher Education Systems"
  "Australian Journal of Environmental Education 31(2), 194-207"
  "2015"
  "10.1017/aee.2015.24"
  "https://doi.org/10.1017/aee.2015.24"
  Attr.academicArticleSource
  "Examines change through a wider institutional system and distinguishes professional knowledge from leadership for change. BOUNDARY: Authorship and studied context do not establish a universal digital higher-education intervention effect."
  Attr.publicAttribution

ryanFerreira2024Source : Attr.AttributedSource
ryanFerreira2024Source = Attr.mkDOISource
  "Lisa D. Ryan; Jo-Anne L. Ferreira"
  "Embedding Sustainability in Teacher Education in Australia"
  "Oxford Research Encyclopedia of Education"
  "2024"
  "10.1093/acrefore/9780190264093.013.1810"
  "https://doi.org/10.1093/acrefore/9780190264093.013.1810"
  Attr.academicArticleSource
  "Reviews policy, curriculum, educator preparation, accreditation and common-vision strategies in embedding EfS. BOUNDARY: A programme case and reference synthesis do not establish measured digital-EfS effects or direct transfer across countries and HE sectors."
  Attr.publicAttribution

blackRyanJiNatureSource : Attr.AttributedSource
blackRyanJiNatureSource = Attr.mkDOISource
  "Ali Black; Lisa Ryan; Okjong Ji (credited with)"
  "Listening to young children with/in nature: Relational, pedagogical and community approaches that work"
  "Young Children and the Environment: Early Education for Sustainability, 3rd ed., chapter 5, pp. 91-119, Cambridge University Press"
  "2024"
  "10.1017/9781009199971.008"
  "https://doi.org/10.1017/9781009199971.008"
  Attr.academicChapterSource
  "Early-childhood nature and community projects in Korea and Australia; relational listening, trust and partnerships. BOUNDARY: Children aged 3-10 and community settings cannot be treated as direct digital higher-education effectiveness evidence; source-specific participation rights must be retained."
  Attr.publicAttribution

ferreiraRyanDavisDeepDiveSource : Attr.AttributedSource
ferreiraRyanDavisDeepDiveSource = Attr.mkDOISource
  "Jo-Anne L. Ferreira; Lisa D. Ryan; Julie M. Davis"
  "A Deep Dive into Sustainability Leadership Through Education for Sustainability"
  "The Palgrave Handbook of Educational Leadership and Management Discourse, pp. 829-849"
  "2022"
  "10.1007/978-3-030-99097-8_68"
  "https://doi.org/10.1007/978-3-030-99097-8_68"
  Attr.academicChapterSource
  "Critically examines sustainability leadership and contested strong/weak sustainability assumptions. BOUNDARY: Scholarly critique and historical framing do not provide direct digital-intervention causal effects or complete authority over community values."
  Attr.publicAttribution

unescoTLSSFSource : Attr.AttributedSource
unescoTLSSFSource = Attr.mkNoDOISource
  "UNESCO (programme owner; Griffith University prepared initial materials with documented contributors)"
  "Teaching and Learning for a Sustainable Future: A Multimedia Teacher Education Programme"
  "UNESCO / Griffith University; multimedia teacher development programme, CD-ROM version 3.0"
  "2002"
  "http://www.unesco.org/education/tlsf/"
  Attr.institutionalSource
  "Institutional multimedia teacher-education programme with 25 modules and around 100 hours of designed professional learning. BOUNDARY: Tool/module availability does not establish observed teacher capacity or transformation. Project participation is not automatically individual authorship."
  Attr.publicAttribution

candidateEfSSources : Attr.AttributedSourceAtlas
candidateEfSSources = Attr.mkSourceAtlas
  "published independent EfS source candidates for cross-pollination"
  "DASHI.Education.DigitalESDEfSSourceCrossPollinationExact"
  (taimurOnukiSource ∷ nilssonDahlstromSource ∷ adefilaEcoCOILSource ∷ singhCommunitySource ∷ barthCompetenciesSource ∷ giridharanCompetenciesSource ∷ jepsenCookeAccessibilitySource ∷ ferreiraRyanTilburySource ∷ ferreiraRyanSystemSource ∷ ferreiraRyanDavisSource ∷ ryanFerreira2024Source ∷ blackRyanJiNatureSource ∷ ferreiraRyanDavisDeepDiveSource ∷ unescoTLSSFSource ∷ Tilbury.tilbury2002 ∷ Tilbury.tilburyWortman2004 ∷ [])
  "Acquisition and candidate interpretive challenge only; exact-study admission requires reviewed source spans, eligibility and claim ceilings."

record CrossPollinationCase : Set where
  constructor source-case
  field
    attributedSource : Attr.AttributedSource
    candidateBridge : Prior.ReciprocalPedagogicalBridge
    sameLocator :
      Prior.EfSSource.exactLocator (Prior.ReciprocalPedagogicalBridge.source candidateBridge)
      ≡ Attr.canonicalURL attributedSource
    admittedToFullReview : Bool
    notYetAdmitted : admittedToFullReview ≡ false
open CrossPollinationCase public

sourceRoleReceipt : (c : CrossPollinationCase) →
  Snowball.SourceRoleSnowballReceipt (attributedSource c)
sourceRoleReceipt c = Snowball.canonicalSourceRoleSnowballReceipt (attributedSource c)

taimurOnuki : CrossPollinationCase
taimurOnuki = source-case taimurOnukiSource
  (Prior.pedagogical-bridge
    Digital.situatedRelationalEngagement Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL taimurOnukiSource) Prior.empiricalContextBound
      "Two university course cases in Japan and Germany; digital/hybrid design-thinking pedagogy; participants' accounts."
      "Reported application of digital transformative pedagogy components in two cases and participant perceptions of learning conditions."
      "No independent proof of durable personal transformation, ecological outcomes, general intervention effects or transfer to other institutions.")
    Prior.productiveTension
    "Digital design thinking is a candidate route to reflective sustainability inquiry, not an automatic transformative learning result."
    "Which observed learning and action indicators distinguish a digitally active design studio from a transformative EfS experience?"
    "Which values, institutional support and participant authority are required before digital design thinking can claim EfS contribution?"
    "Positive course experiences can coexist with unchanged sustainability competence or limited long-term action."
    "Independent competence measures, realised sample, timing, counterexamples, educator practice and ecological/social consequence follow-up."
    Prior.candidate refl)
  refl false refl

nilssonDahlstrom : CrossPollinationCase
nilssonDahlstrom = source-case nilssonDahlstromSource
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.valuesAndCriticalReflection
    (Prior.efs-source (Attr.canonicalURL nilssonDahlstromSource) Prior.crossPaperInterpretation
      "Scoping review of social sustainability in education, publications 2018-2023; 42 articles in final analysis."
      "Documents differences and conceptual/assessment difficulties in definitions and enactment of social sustainability."
      "The review's denominators and synthesis belong to its author; they cannot pay Digital-ESD's database, admission or outcome obligations.")
    Prior.productiveTension
    "Explicit social-sustainability definitions must precede any translation of digital-learning research into sustainability impact."
    "What does the original study observe that can distinguish equity, belonging and participation from general digital activity?"
    "Which explicit meaning of social sustainability and whose normative authority controls the analytic categories?"
    "Different social-sustainability definitions can make a digital outcome positive under one reading and incomplete under another."
    "Independent review coding and source-span comparison; operational definitions, affected groups and empirical indicators."
    Prior.candidate refl)
  refl false refl

adefilaEcoCOIL : CrossPollinationCase
adefilaEcoCOIL = source-case adefilaEcoCOILSource
  (Prior.pedagogical-bridge
    Digital.constitutiveLearnerAgency Prior.participationAndCollectiveAction
    (Prior.efs-source (Attr.canonicalURL adefilaEcoCOILSource) Prior.practitionerTheoretical
      "EcoCOIL proposal for transnational digital collaboration involving students, community organisations and varied stakeholders."
      "Models participatory co-creation, intercultural participation, coalition building and sustainability problem inquiry in digital settings."
      "Conceptual/model claims are not independent measurement of community authority, collective impacts or ecological outcomes.")
    Prior.productiveTension
    "Digital collaboration may support collective EfS inquiry only if communities retain consequential roles in decisions and knowledge production."
    "Who can set the problem, contest its framing and change decisions in the shared online collaboration?"
    "Does an international digital collaboration create community benefit, or merely more institutional activity and visibility?"
    "Nominal partnership can conceal unequal decision rights, digital burden or extractive knowledge flows."
    "Source-specific enactment, community decision rights, benefit/burden distribution and long-term outcomes."
    Prior.candidate refl)
  refl false refl

singhCommunity : CrossPollinationCase
singhCommunity = source-case singhCommunitySource
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.participationAndCollectiveAction
    (Prior.efs-source (Attr.canonicalURL singhCommunitySource) Prior.crossPaperInterpretation
      "Literature review of community-engaged teaching and learning and sustainable development in higher education."
      "Reviews pedagogical arrangements, community partnerships, sustainability competencies and conditions that constrain enactment."
      "Review-level reports do not demonstrate causal effects of a specific digital intervention or authorise a university to speak for community partners.")
    Prior.productiveTension
    "Community-engaged learning requires distinct knowledge owners and reciprocal partnership, not a single university observer."
    "Can digital teaching retain community-defined research problems and participation in interpreting the results?"
    "Which local stakeholders can refuse, revise or challenge a sustainability learning intervention?"
    "Institutionally assessed service learning can report student benefit while concealing community burdens."
    "Community-authored source spans, partnership authority, project outcomes and critical negative cases."
    Prior.candidate refl)
  refl false refl

barthCompetencies : CrossPollinationCase
barthCompetencies = source-case barthCompetenciesSource
  (Prior.pedagogical-bridge
    Digital.situatedRelationalEngagement Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL barthCompetenciesSource) Prior.empiricalContextBound
      "Exploratory qualitative focus groups about formal and informal learning in higher education."
      "Identifies roles for cognitive and non-cognitive dispositions, multiple learning contexts and student responsibility in competence development."
      "Original authors identify remaining uncertainty about interdependencies; no digital intervention comparison or universal causal mechanism.")
    Prior.mutuallyRefining
    "Formal and informal learner environments may jointly support competence but must not be inferred from visible platform engagement."
    "What learning evidence links digital participation to sustainability reasoning across contexts and time?"
    "Which informal community, interdisciplinary and practice contexts are absent from an institution's learning analytics?"
    "A digitally intensive course may generate activity without competence beyond the course setting."
    "Cross-context performance assessment, informal-learning measures and longitudinal study design."
    Prior.candidate refl)
  refl false refl

giridharanCompetencies : CrossPollinationCase
giridharanCompetencies = source-case giridharanCompetenciesSource
  (Prior.pedagogical-bridge
    Digital.iterativeEvidenceReturnAndRecharting Prior.futuresAndIntergenerationalThinking
    (Prior.efs-source (Attr.canonicalURL giridharanCompetenciesSource) Prior.practitionerTheoretical
      "Higher-education leadership and key-competency chapter concerning technological change and institutional sustainability."
      "Develops a strategic account of future-facing competencies, flexible learning, digital provision and changing institutional models."
      "Conceptual and policy-facing discussion does not supply measured evidence of sustainability competence, durability or employment benefit.")
    Prior.complementary
    "Future-facing competencies require repeated reinterpretation of contexts, not automatic extrapolation from new digital tools."
    "What evidence would show adaptable and context-sensitive competencies instead of digital skill claims alone?"
    "How are financial, social and temporal burdens included in prospective higher-education learning plans?"
    "Digital flexibility may relocate costs onto learners while appearing to improve institutional resilience."
    "Versioned policy framework, institutional finance and learner outcome evidence from the relevant setting."
    Prior.candidate refl)
  refl false refl

jepsenCookeAccessibility : CrossPollinationCase
jepsenCookeAccessibility = source-case jepsenCookeAccessibilitySource
  (Prior.pedagogical-bridge
    Digital.adaptiveSupportWithLocalChoice Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL jepsenCookeAccessibilitySource) Prior.practitionerTheoretical
      "Industry/conference paper on digital accessibility and heterogeneous higher-education disability contexts."
      "Argues that design must accommodate conflicting access needs and context-specific learner constraints."
      "Industry perspective and advocated outcomes do not establish audited disability accessibility, retention effects or causal employment outcomes.")
    Prior.productiveTension
    "Universal availability and a fixed accessibility setting cannot substitute for situated effective access and user choice."
    "Does a claimed accessible digital platform preserve assistive workflow and multiple conflicting access requirements?"
    "Who may choose adjustments, report harms and seek practical repair without being excluded?"
    "An accessibility change that benefits one person can impede another person."
    "Relevant disability and intersectionality perspectives, effective task completion, assistive tooling and adverse-event reports."
    Prior.candidate refl)
  refl false refl

ferreiraRyanTilbury : CrossPollinationCase
ferreiraRyanTilbury = source-case ferreiraRyanTilburySource
  (Prior.pedagogical-bridge
    Digital.situatedRelationalEngagement Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanTilburySource) Prior.crossPaperInterpretation
      "Review and critique of professional development for EfS in Australian initial teacher education."
      "Separates resource delivery, professional learning and more systemic change approaches in teacher education."
      "Initial teacher education context and professional-development models do not independently establish effects in digital university teaching.")
    Prior.productiveTension
    "Pedagogical resources are necessary inputs but not the same as institutional EfS enactment."
    "How do digital-learning educators acquire capacity and decision rights to enact sustainability pedagogy?"
    "What enduring supports and professional-development conditions distinguish sustainability implementation from content availability?"
    "More digital resources can coexist with little pedagogical change."
    "Professional-development process, teaching-practice and cross-institutional transfer evidence."
    Prior.candidate refl)
  refl false refl

ferreiraRyanSystem : CrossPollinationCase
ferreiraRyanSystem = source-case ferreiraRyanSystemSource
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanSystemSource) Prior.empiricalContextBound
      "Australian pre-service teacher education systems; resource-development, action-research and contextual-change models."
      "Studies organisational curriculum change and proposes an integrated Mainstreaming Change model across system levels."
      "Proposed systems model is not proof of general digital-ESD or longitudinal intervention outcomes.")
    Prior.mutuallyRefining
    "Systemic change requires linked institutional, curricular and professional conditions rather than a successful isolated digital lesson."
    "Can a digital innovation change linked incentives, training, governance and curriculum beyond the local teaching activity?"
    "Which institutional dependencies make apparently successful digital EfS work fail to endure?"
    "An excellent course can coexist with unchanged structural incentives."
    "Policy-level actions, implementation trajectories, durability and contradictory cases."
    Prior.candidate refl)
  refl false refl

ferreiraRyanDavis : CrossPollinationCase
ferreiraRyanDavis = source-case ferreiraRyanDavisSource
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanDavisSource) Prior.empiricalContextBound
      "Pre-service teacher education organisations and their interconnected leadership context."
      "Examines change through a wider institutional system and distinguishes professional knowledge from leadership for change."
      "Authorship and studied context do not establish a universal digital higher-education intervention effect.")
    Prior.productiveTension
    "Teacher expertise and distributed system leadership are separate conditions of institution-wide EfS enactment."
    "Which actors can alter digital-ESD curriculum, policy and professional learning beyond an individual teacher?"
    "Can a project survive after its initiating educator or funding arrangement changes?"
    "Individual teacher competence may improve while the system still blocks institution-wide action."
    "Leadership roles, decision rights, cross-level evidence and persistence over time."
    Prior.candidate refl)
  refl false refl

ryanFerreira2024 : CrossPollinationCase
ryanFerreira2024 = source-case ryanFerreira2024Source
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL ryanFerreira2024Source) Prior.crossPaperInterpretation
      "Australian teacher education and decade-scale system-change case context; Oxford Research Encyclopedia reference article."
      "Reviews policy, curriculum, educator preparation, accreditation and common-vision strategies in embedding EfS."
      "A programme case and reference synthesis do not establish measured digital-EfS effects or direct transfer across countries and HE sectors.")
    Prior.productiveTension
    "Effective EfS integration depends on curricula, professional standards, shared purposes and institutional structures."
    "Are digital-ESD proposals embedded in governance and educator capacity, or restricted to one technology project?"
    "Which policy/accreditation and stakeholder conditions permit long-term transformative ESD?"
    "Programme-level adoption can exist without meaningful learner competence or equity."
    "Timeline, governance, implementation and outcomes under transparent study-specific evidence limits."
    Prior.candidate refl)
  refl false refl

tilburyIUCN2002 : CrossPollinationCase
tilburyIUCN2002 = source-case Tilbury.tilbury2002
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.systemsRelationships
    (Prior.efs-source (Attr.canonicalURL Tilbury.tilbury2002) Prior.crossPaperInterpretation
      "Edited IUCN case collection about education and sustainability; chapter claims must be separately sourced."
      "Plural educational and community pathways for sustainability."
      "An edited case collection does not assign every case a common method or prove context-free impact.")
    Prior.complementary
    "Retain distinct routes to sustainability education without inventing an exhaustive ESD mechanism."
    "Which situated source and respondent support each distinct proposed digital-to-ESD pathway?"
    "Which cases have been left out of the digital comparison?"
    "A general book-level theme can conceal contradictory cases."
    "Chapter-level source spans, role attribution and review decisions."
    Prior.candidate refl)
  refl false refl

tilburyWortman2004 : CrossPollinationCase
tilburyWortman2004 = source-case Tilbury.tilburyWortman2004
  (Prior.pedagogical-bridge
    Digital.constitutiveLearnerAgency Prior.participationAndCollectiveAction
    (Prior.efs-source (Attr.canonicalURL Tilbury.tilburyWortman2004) Prior.practitionerTheoretical
      "IUCN sustainability engagement handbook; five documented practice themes."
      "Futures, critical reflection, participation in decisions, partnership and systemic thinking."
      "A practitioner framework is not a controlled effectiveness study or evidence of community consent.")
    Prior.mutuallyRefining
    "Collective decision roles need to be observed separately from learner voice and platform engagement."
    "Can participants revise the question and act on contested sustainability decisions?"
    "Whose power to decide, refuse or exit remains absent?"
    "Consultation may be labelled participation without actually changing decisions."
    "Decision-process evidence, community source roles and sustained action."
    Prior.candidate refl)
  refl false refl

blackRyanJiNature : CrossPollinationCase
blackRyanJiNature = source-case blackRyanJiNatureSource
  (Prior.pedagogical-bridge
    Digital.pluralSituatedObservers Prior.ecologicalAndMoreThanHumanRelations
    (Prior.efs-source (Attr.canonicalURL blackRyanJiNatureSource)
      Prior.empiricalContextBound
      "Early-childhood education for sustainability in Australian and Korean nature/community projects."
      "Source discusses relational listening to children, shared goals, partners and ecological/community participation."
      "No direct transfer to university digital learning, and adult interpretations cannot stand in for child voice or other-than-human testimony.")
    Prior.productiveTension
    "A situated learner/child/community observer may contest institutional assumptions about ecological education."
    "How could digital higher education retain participant/partner authority rather than treating engagement surveys as sufficient?"
    "What non-human ecological relationships and community decisions remain unobserved by an online course?"
    "Adult-led nature activities can be labelled participatory without granting consequential agency."
    "Participant voice, community decisions, ecological observations, population-transfer and outcome review."
    Prior.candidate refl)
  refl false refl

ferreiraRyanDavisDeepDive : CrossPollinationCase
ferreiraRyanDavisDeepDive = source-case ferreiraRyanDavisDeepDiveSource
  (Prior.pedagogical-bridge
    Digital.contextualCustodianship Prior.valuesAndCriticalReflection
    (Prior.efs-source (Attr.canonicalURL ferreiraRyanDavisDeepDiveSource)
      Prior.crossPaperInterpretation
      "Critical sustainability leadership chapter in a published handbook."
      "Examines the competing normative traditions and disrupted histories of education for sustainability."
      "Critical-theoretical genealogy does not itself prove learning, implementation or system change.")
    Prior.productiveTension
    "Historical, political and normative ESD distinctions constrain how a digital innovation can claim transformation."
    "Which sustainability vision and organisational interests are presupposed by the digital education evaluation?"
    "Can learners and communities contest weak or purely technocratic interpretations of sustainability?"
    "An apparently successful digital innovation can satisfy a narrow sustainability metric while reinforcing an inequitable governance structure."
    "Explicit normative frame, competing perspectives, participant authority, policy context and same-object observations."
    Prior.candidate refl)
  refl false refl

unescoTLSSF : CrossPollinationCase
unescoTLSSF = source-case unescoTLSSFSource
  (Prior.pedagogical-bridge
    Digital.iterativeEvidenceReturnAndRecharting Prior.transformativeEducatorPraxis
    (Prior.efs-source (Attr.canonicalURL unescoTLSSFSource)
      Prior.practitionerTheoretical
      "UNESCO institutional teacher-education multimedia programme of 25 modules, around 100 hours."
      "Programme design supports educator learning opportunities concerning ESD and multimedia methods."
      "The programme's existence, duration and activity descriptions do not establish competence, uptake, durable practice or impact.")
    Prior.complementary
    "An early institutional digital EfS programme provides a prior-art example of designed teacher capacity support."
    "Which observed teacher practices distinguish multimedia availability from sustained ESD enactment?"
    "Can educator professional learning retain values reflection and system transformation rather than only digital content delivery?"
    "A large module count is an implementation input and cannot be promoted to a sustainable learning outcome."
    "Training exposure, teacher practice changes, student outcomes, adoption across institutions and longitudinal follow-up."
    Prior.candidate refl)
  refl false refl

canonicalSourceCases : List CrossPollinationCase
canonicalSourceCases =
  taimurOnuki ∷
  nilssonDahlstrom ∷
  adefilaEcoCOIL ∷
  singhCommunity ∷
  barthCompetencies ∷
  giridharanCompetencies ∷
  jepsenCookeAccessibility ∷
  ferreiraRyanTilbury ∷
  ferreiraRyanSystem ∷
  ferreiraRyanDavis ∷
  ryanFerreira2024 ∷
  blackRyanJiNature ∷
  ferreiraRyanDavisDeepDive ∷
  unescoTLSSF ∷
  tilburyIUCN2002 ∷
  tilburyWortman2004 ∷ []

-- Reuse the existing evidence braid rather than manufacture a second
-- convergence / conflict / epistemic-authority ontology.
relationFor : Prior.BridgeStatus → Braid.BraidRelation
relationFor Prior.complementary = Braid.complementarity
relationFor Prior.mutuallyRefining = Braid.convergence
relationFor Prior.productiveTension = Braid.productiveTension
relationFor Prior.unresolved = Braid.unresolvedConflict

canonicalBraid : CrossPollinationCase → Braid.TensionReceipt
canonicalBraid c = Braid.tension-receipt
  (Attr.canonicalURL (attributedSource c))
  "DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact"
  (Attr.canonicalURL (attributedSource c))
  "DASHI.Biology.EducationCorpusSourceRegistry"
  (relationFor (Prior.ReciprocalPedagogicalBridge.status (candidateBridge c)))
  (Prior.ReciprocalPedagogicalBridge.competingReading (candidateBridge c))

candidateEvidenceDebt : CrossPollinationCase → String
candidateEvidenceDebt c =
  Prior.ReciprocalPedagogicalBridge.evidenceDebt (candidateBridge c)

data CitationCreatesSourceAdmission : Set where
data SourceComparisonEstablishesInterventionEffect : Set where
data PreSearchCrosswalkEstablishesPublicationNovelty : Set where
data EditorInvitationCreatesScholarshipAuthority : Set where
data EarlierReviewPaysDigitalESDSearchExecution : Set where
data UniversityVoiceOverridesCommunityAuthority : Set where
data ContextFreeSustainabilityCompetence : Set where

citationDoesNotAdmitSource : CitationCreatesSourceAdmission → ⊥
citationDoesNotAdmitSource ()
comparisonDoesNotProveEffect : SourceComparisonEstablishesInterventionEffect → ⊥
comparisonDoesNotProveEffect ()
crosswalkDoesNotProveNovelty : PreSearchCrosswalkEstablishesPublicationNovelty → ⊥
crosswalkDoesNotProveNovelty ()
invitationDoesNotCreateAuthority : EditorInvitationCreatesScholarshipAuthority → ⊥
invitationDoesNotCreateAuthority ()
otherReviewDoesNotPaySearch : EarlierReviewPaysDigitalESDSearchExecution → ⊥
otherReviewDoesNotPaySearch ()
universityDoesNotOverrideCommunity : UniversityVoiceOverridesCommunityAuthority → ⊥
universityDoesNotOverrideCommunity ()
competenceIsNotContextFree : ContextFreeSustainabilityCompetence → ⊥
competenceIsNotContextFree ()
