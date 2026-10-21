module DASHI.Education.DigitalESDEfSPedagogicalReciprocityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Digital

-- Two independently sourced pedagogical traditions. The EfS concepts below
-- are an interpretive coding vocabulary, NOT an empirical result or a complete
-- taxonomy of EfS/ESD theory.
data EfSPedagogicalOrientation : Set where
  systemsRelationships : EfSPedagogicalOrientation
  valuesAndCriticalReflection : EfSPedagogicalOrientation
  futuresAndIntergenerationalThinking : EfSPedagogicalOrientation
  participationAndCollectiveAction : EfSPedagogicalOrientation
  ecologicalAndMoreThanHumanRelations : EfSPedagogicalOrientation
  transformativeEducatorPraxis : EfSPedagogicalOrientation

data EvidenceRole : Set where
  empiricalContextBound : EvidenceRole
  practitionerTheoretical : EvidenceRole
  crossPaperInterpretation : EvidenceRole

data BridgeStatus : Set where
  complementary : BridgeStatus
  mutuallyRefining : BridgeStatus
  productiveTension : BridgeStatus
  unresolved : BridgeStatus

data Promotion : Set where
  candidate : Promotion
  sourceReviewed : Promotion
  empiricallySupported : Promotion

record EfSSource : Set where
  constructor efs-source
  field
    exactLocator : String
    sourceRole : EvidenceRole
    scope : String
    boundedContribution : String
    doesNotEstablish : String
open EfSSource public

vikaneHoydalsvik : EfSSource
vikaneHoydalsvik = efs-source
  "https://doi.org/10.1080/13504622.2023.2273785"
  empiricalContextBound
  "Norwegian early-childhood education; Vikane and Høydalsvik, published online 2023, volume 2024"
  "Teachers' expressed understandings and reported/practised EfS pedagogy: contextual evidence about the difference between sustainability topics and transformative practice."
  "No universal EfS pedagogy distribution; no digital-education intervention effect."

elliottEfS : EfSSource
elliottEfS = efs-source
  "https://www.earlychildhoodaustralia.org.au/the-spoke/education-for-sustainability/"
  practitionerTheoretical
  "Elliott 2019, Early Childhood Australia practitioner/theoretical EfS account"
  "Critical reflection; ecological relationships; present and future children; advocacy and action beyond recycling/composting activities."
  "Not a controlled intervention trial, quantitative impact estimate or universal causal result."

record ReciprocalPedagogicalBridge : Set where
  constructor pedagogical-bridge
  field
    digitalPrinciple : Digital.TransferablePedagogicalPrinciple
    efsOrientation : EfSPedagogicalOrientation
    source : EfSSource
    status : BridgeStatus
    mechanismHypothesis : String
    digitalToEfSQuestion : String
    efsToDigitalQuestion : String
    competingReading : String
    evidenceDebt : String
    promotion : Promotion
    candidateOnly : promotion ≡ candidate
open ReciprocalPedagogicalBridge public

systemsCustodianship : ReciprocalPedagogicalBridge
systemsCustodianship = pedagogical-bridge
  Digital.contextualCustodianship systemsRelationships elliottEfS mutuallyRefining
  "Situated data interpretation can preserve relational ecological context rather than model learners as context-free data points."
  "Can collaborative digital modelling help students investigate interdependent ecological and social systems?"
  "Can students interrogate boundaries, assumptions and absent ecological relationships in digital models?"
  "System visualisation may increase activity without demonstrating systems understanding."
  "Independent learning assessment, setting, learner voice, model-boundary review and outcome measurement."
  candidate refl

reflectionFeedback : ReciprocalPedagogicalBridge
reflectionFeedback = pedagogical-bridge
  Digital.feedbackAsRevisableSignal valuesAndCriticalReflection elliottEfS productiveTension
  "Feedback can become material for critical examination of assumptions and value judgments rather than a fixed correctness signal."
  "Can feedback tools help learners justify and revise contested sustainability values?"
  "Can learners question the categories/values embedded in an automated response?"
  "Optimisation for predeclared answers may suppress open normative disagreement."
  "Participant interpretation, plural value positions, task evidence and safe contestation procedure."
  candidate refl

collectiveAgency : ReciprocalPedagogicalBridge
collectiveAgency = pedagogical-bridge
  Digital.constitutiveLearnerAgency participationAndCollectiveAction elliottEfS mutuallyRefining
  "Student participation in inquiry may be extended to shared ecological/community decisions."
  "Can digital co-design help learners participate in collective sustainability action?"
  "Does individual choice displace collective deliberation or decision authority?"
  "Individual platform engagement is not collective efficacy or actual decision power."
  "Real decision authority, downstream action, inclusion, group process and outcome follow-up."
  candidate refl

futuresRechart : ReciprocalPedagogicalBridge
futuresRechart = pedagogical-bridge
  Digital.iterativeEvidenceReturnAndRecharting futuresAndIntergenerationalThinking elliottEfS complementary
  "Iterated scenarios can be revised against evidence while keeping alternative futures open."
  "Can digital futures exercises preserve multiple possible futures and iterative revision?"
  "Can learners challenge presentist optimisation and represent future generations without appropriating their voice?"
  "Scenario generation is not predictive validity or improved future outcomes."
  "Horizon, scenario assumptions, interpretation, follow-up and option-preservation receipts."
  candidate refl

ecologicalObservers : ReciprocalPedagogicalBridge
ecologicalObservers = pedagogical-bridge
  Digital.pluralSituatedObservers ecologicalAndMoreThanHumanRelations elliottEfS productiveTension
  "Ecological consequences can be observed through explicit methods alongside human testimony."
  "Which non-human and ecosystem effects are missing from a digital teaching account?"
  "How can ecological evidence inform decisions without attributing speech or consent to non-human entities?"
  "Representing ecosystems through indicators is not their first-person testimony."
  "Source-bounded ecological observations, governance legitimacy and attribution boundaries."
  candidate refl

educatorPraxis : ReciprocalPedagogicalBridge
educatorPraxis = pedagogical-bridge
  Digital.situatedRelationalEngagement transformativeEducatorPraxis vikaneHoydalsvik productiveTension
  "Pedagogy depends on how educators understand and enact sustainability, not merely which topics are present."
  "Can digital teaching support inquiry and educator professional learning beyond topic coverage?"
  "Do the activities show transformative pedagogy or only discussion of sustainability?"
  "An early-childhood Norwegian sample cannot directly determine Australian higher-education practice."
  "Independent situated implementation observations, competence assessment, teacher collaboration and context-transfer review."
  candidate refl

localChoiceCollectiveTension : ReciprocalPedagogicalBridge
localChoiceCollectiveTension = pedagogical-bridge
  Digital.adaptiveSupportWithLocalChoice participationAndCollectiveAction elliottEfS productiveTension
  "Flexible individual support may either enable or fragment participation in collective sustainability inquiry."
  "Does adaptive support enable currently excluded learners to join shared action?"
  "Does personalisation privatise what should be collectively negotiated?"
  "No automatic universal compatibility or conflict between personalisation and collective action."
  "Comparative learner participation and collective outcomes, contextual mediation, and accessibility evidence."
  candidate refl

canonicalReciprocalCandidates : List ReciprocalPedagogicalBridge
canonicalReciprocalCandidates =
  systemsCustodianship ∷ reflectionFeedback ∷ collectiveAgency ∷
  futuresRechart ∷ ecologicalObservers ∷ educatorPraxis ∷
  localChoiceCollectiveTension ∷ []

-- The original digital seven are not automatically validated by new EfS
-- sources; source roles and context-transfer gates are independent.
data TheoreticalAlignmentProvesEffect : Set where
data EfSSourceProvesDigitalIntervention : Set where
data NorwegianECEFindingsAutomaticallyTransferToHE : Set where
data PractitionerArgumentCreatesCausalEffect : Set where
data IndividualChoiceCreatesCollectiveAuthority : Set where

alignmentIsNotEffect : TheoreticalAlignmentProvesEffect → ⊥
alignmentIsNotEffect ()
efsSourceDoesNotProveDigitalIntervention : EfSSourceProvesDigitalIntervention → ⊥
efsSourceDoesNotProveDigitalIntervention ()
noAutomaticECEToHETransfer : NorwegianECEFindingsAutomaticallyTransferToHE → ⊥
noAutomaticECEToHETransfer ()
noPractitionerCausalPromotion : PractitionerArgumentCreatesCausalEffect → ⊥
noPractitionerCausalPromotion ()
choiceDoesNotCreateCollectiveAuthority : IndividualChoiceCreatesCollectiveAuthority → ⊥
choiceDoesNotCreateCollectiveAuthority ()
