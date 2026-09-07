module DASHI.Cognition.PNF.SensibLawInternationalObligationDomesticRemedyTranslationExact where

------------------------------------------------------------------------
-- INTERNATIONAL LEGAL OBLIGATION != AUTOMATIC DOMESTIC CAUSE OF ACTION
--
-- Primary source / stable identifier:
--   International Court of Justice, Legal Consequences arising from the
--   Policies and Practices of Israel in the Occupied Palestinian Territory,
--   including East Jerusalem, Advisory Opinion, 19 July 2024,
--   General List No 186, document 186-20240719-ADV-01-00-EN,
--   https://www.icj-cij.org/node/204160
--   Summary: https://www.icj-cij.org/node/204176
--
-- Source-backed propositions represented here include the Court's conclusions
-- that Israel's continued presence in the Occupied Palestinian Territory is
-- unlawful; Israel must end that presence as rapidly as possible, cease new
-- settlement activity, and make reparation; and all States have obligations of
-- non-recognition and non-assistance in relation to the unlawful situation.
--
-- The domestic translation graph below is DASHI reconstruction. This module
-- does NOT assert that the Advisory Opinion creates any particular Australian
-- private-law cause of action, standing rule, duty of care, compensable damage
-- head, or executable Australian remedy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge

icj2024PalestineAuthority : Edge.SourceIdentity
icj2024PalestineAuthority = Edge.source-identity
  "International Court of Justice"
  "Legal Consequences arising from the Policies and Practices of Israel in the Occupied Palestinian Territory, including East Jerusalem, Advisory Opinion"
  "General List No 186; 186-20240719-ADV-01-00-EN; 19 July 2024; https://www.icj-cij.org/node/204160"
  Edge.internationalJudicialOpinion

data NormativeLayer : Set where
  fact : NormativeLayer
  legalStatus : NormativeLayer
  legalObligation : NormativeLayer
  domesticCauseOfAction : NormativeLayer
  domesticDuty : NormativeLayer
  breach : NormativeLayer
  compensableDamage : NormativeLayer
  availableRemedy : NormativeLayer
  executableRemedy : NormativeLayer


record LayerClaim : Set where
  constructor layer-claim
  field
    layer : NormativeLayer
    proposition : String
    authority : Edge.SourceIdentity
    sourceBacked : Bool

open LayerClaim public

icjUnlawfulPresence : LayerClaim
icjUnlawfulPresence = layer-claim legalStatus
  "Israel's continued presence in the Occupied Palestinian Territory is unlawful"
  icj2024PalestineAuthority true

icjEndPresenceObligation : LayerClaim
icjEndPresenceObligation = layer-claim legalObligation
  "Israel is under an obligation to bring its unlawful presence to an end as rapidly as possible"
  icj2024PalestineAuthority true

icjReparationObligation : LayerClaim
icjReparationObligation = layer-claim legalObligation
  "Israel is under an obligation to make reparation for damage caused to the natural or legal persons concerned"
  icj2024PalestineAuthority true

icjOtherStatesNonRecognition : LayerClaim
icjOtherStatesNonRecognition = layer-claim legalObligation
  "all States are under an obligation not to recognize as legal the situation arising from the unlawful presence and not to render aid or assistance in maintaining it"
  icj2024PalestineAuthority true

data TranslationGate : Set where
  domesticReceptionRule : TranslationGate
  jurisdiction : TranslationGate
  standing : TranslationGate
  causeOfAction : TranslationGate
  duty : TranslationGate
  breachGate : TranslationGate
  causation : TranslationGate
  damageRecognition : TranslationGate
  remedyJurisdiction : TranslationGate
  executionMechanism : TranslationGate


record TranslationRequirement : Set where
  constructor translation-requirement
  field
    fromLayer : NormativeLayer
    toLayer : NormativeLayer
    gate : TranslationGate
    proposition : String
    independentlyRequired : Bool

open TranslationRequirement public

internationalToDomesticAction : TranslationRequirement
internationalToDomesticAction = translation-requirement
  legalObligation domesticCauseOfAction domesticReceptionRule
  "an international-law obligation does not by itself instantiate an Australian domestic private cause of action"
  true

domesticActionToRemedy : TranslationRequirement
domesticActionToRemedy = translation-requirement
  domesticCauseOfAction availableRemedy remedyJurisdiction
  "a domestic cause of action still requires its own duty/standing/elements/damage/remedy gates"
  true

data InternationalObligationAutomaticallyCreatesDomesticCauseOfAction : Set where
data LegalStatusAutomaticallyCreatesRemedy : Set where
data LegalObligationAutomaticallyCreatesExecutableRemedy : Set where
data NoAutomaticDomesticRemedyMeansInternationalLawHasNoTeeth : Set where
data SameRecognitionRemedyGapMeansSameDoctrine : Set where

internationalObligationDoesNotAutoCreateDomesticAction :
  InternationalObligationAutomaticallyCreatesDomesticCauseOfAction → ⊥
internationalObligationDoesNotAutoCreateDomesticAction ()

statusDoesNotAutoCreateRemedy : LegalStatusAutomaticallyCreatesRemedy → ⊥
statusDoesNotAutoCreateRemedy ()

obligationDoesNotAutoCreateExecutableRemedy :
  LegalObligationAutomaticallyCreatesExecutableRemedy → ⊥
obligationDoesNotAutoCreateExecutableRemedy ()

translationGapDoesNotEraseInternationalObligation :
  NoAutomaticDomesticRemedyMeansInternationalLawHasNoTeeth → ⊥
translationGapDoesNotEraseInternationalObligation ()

sharedTopologyDoesNotCollapseDoctrine : SameRecognitionRemedyGapMeansSameDoctrine → ⊥
sharedTopologyDoesNotCollapseDoctrine ()

record RecognitionRemedyLattice : Set where
  constructor recognition-remedy-lattice
  field
    factRecognised : Bool
    legalStatusRecognised : Bool
    legalObligationRecognised : Bool
    domesticRemedyAvailable : Bool
    descentGuaranteed : Bool

open RecognitionRemedyLattice public

icjAdvisoryCalibration : RecognitionRemedyLattice
icjAdvisoryCalibration = recognition-remedy-lattice true true true false false

recognitionCanOutrunDomesticRemedy :
  descentGuaranteed icjAdvisoryCalibration ≡ false
recognitionCanOutrunDomesticRemedy = refl
