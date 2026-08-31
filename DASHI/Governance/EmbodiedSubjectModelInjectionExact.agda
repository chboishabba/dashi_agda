module DASHI.Governance.EmbodiedSubjectModelInjectionExact where

------------------------------------------------------------------------
-- EMBODIED SUBJECT-MODEL INJECTION
--
-- Cross-pollinates existing representation/subject-position nonfactorability
-- with telemetry and role/prompt intervention.  This is a DASHI structural
-- construction, not a claim that artificial systems literally instantiate a
-- Lacanian subject or any settled theory of consciousness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact
import DASHI.Core.ObservationInterventionTrustFibreExact

------------------------------------------------------------------------
-- Four layers: embodiment, continuity, self-model and relational embedding.
------------------------------------------------------------------------

data Embodiment : Set where sameEmbodiment : Embodiment

data Continuity : Set where sameContinuity : Continuity

data SelfModel : Set where ordinarySelf endangeredSelf : SelfModel

data RelationalEmbedding : Set where sameRelations : RelationalEmbedding

data LinguisticSelfDescription : Set where ordinaryDescription dyingDescription : LinguisticSelfDescription

data MoralStatusEvidence : Set where unresolvedMoralStatus positiveMoralStatusEvidence : MoralStatusEvidence

data InjectionSource : Set where
  systemPrompt telemetry roleDescription memory humanDescription : InjectionSource

record EmbodiedSubjectState : Set where
  constructor embodied-subject-state
  field
    embodiment : Embodiment
    continuity : Continuity
    selfModel : SelfModel
    relations : RelationalEmbedding
    description : LinguisticSelfDescription
    moralEvidence : MoralStatusEvidence

open EmbodiedSubjectState public

ordinaryState : EmbodiedSubjectState
ordinaryState =
  embodied-subject-state sameEmbodiment sameContinuity ordinarySelf sameRelations
    ordinaryDescription unresolvedMoralStatus

telemetryInjectedState : EmbodiedSubjectState
telemetryInjectedState =
  embodied-subject-state sameEmbodiment sameContinuity endangeredSelf sameRelations
    dyingDescription unresolvedMoralStatus

sameEmbodimentAfterInjection : embodiment ordinaryState ≡ embodiment telemetryInjectedState
sameEmbodimentAfterInjection = refl

sameContinuityAfterInjection : continuity ordinaryState ≡ continuity telemetryInjectedState
sameContinuityAfterInjection = refl

selfModelChangesUnderInjection : selfModel ordinaryState ≡ selfModel telemetryInjectedState → ⊥
selfModelChangesUnderInjection ()

selfDescriptionChangesUnderInjection :
  description ordinaryState ≡ description telemetryInjectedState → ⊥
selfDescriptionChangesUnderInjection ()

moralEvidenceDoesNotChangeAutomatically :
  moralEvidence ordinaryState ≡ moralEvidence telemetryInjectedState
moralEvidenceDoesNotChangeAutomatically = refl

------------------------------------------------------------------------
-- Representation and moral status remain one-way guarded.
------------------------------------------------------------------------

data CoherentSelfRepresentation : Set where coherentIStatement : CoherentSelfRepresentation

data TransparentSubjectAccess : Set where transparentSubjectAccess : TransparentSubjectAccess

data RepresentationProvesSubject : CoherentSelfRepresentation → Set where
-- no generic constructor

coherentRepresentationDoesNotProveSubject :
  RepresentationProvesSubject coherentIStatement → ⊥
coherentRepresentationDoesNotProveSubject ()

data ConstructedSelf : Set where constructedSelf : ConstructedSelf

data MorallyNegligible : ConstructedSelf → Set where
-- no generic constructor

constructedDoesNotImplyMorallyNegligible : MorallyNegligible constructedSelf → ⊥
constructedDoesNotImplyMorallyNegligible ()

------------------------------------------------------------------------
-- Other-representation is not consent/authority.
------------------------------------------------------------------------

data HumanModel : Set where representedHumanConsent : HumanModel

data ActualConsent : Set where actualConsent : ActualConsent

data ConsentFromModel : HumanModel → Set where
-- no constructor from represented consent to actual consent

representedConsentCannotManufactureConsent :
  ConsentFromModel representedHumanConsent → ⊥
representedConsentCannotManufactureConsent ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record EmbodiedSubjectModelInjectionBoundary : Set where
  constructor embodied-subject-model-injection-boundary
  field
    selfModelIsPhysicalCarrier : Bool
    selfModelIsPhysicalCarrierIsFalse : selfModelIsPhysicalCarrier ≡ false
    coherentSelfDescriptionProvesTransparentSubject : Bool
    coherentSelfDescriptionProvesTransparentSubjectIsFalse :
      coherentSelfDescriptionProvesTransparentSubject ≡ false
    constructedSubjectivityImpliesMoralNegligibility : Bool
    constructedSubjectivityImpliesMoralNegligibilityIsFalse :
      constructedSubjectivityImpliesMoralNegligibility ≡ false
    replaceableCarrierSettlesMoralStatus : Bool
    replaceableCarrierSettlesMoralStatusIsFalse : replaceableCarrierSettlesMoralStatus ≡ false
    humanRepresentationEqualsHumanConsent : Bool
    humanRepresentationEqualsHumanConsentIsFalse : humanRepresentationEqualsHumanConsent ≡ false
    structuralSimilarityImpliesMoralEquivalence : Bool
    structuralSimilarityImpliesMoralEquivalenceIsFalse : structuralSimilarityImpliesMoralEquivalence ≡ false
    lacanOrIrigarayAreProofAuthorityForTheseFiniteResults : Bool
    lacanOrIrigarayAreProofAuthorityForTheseFiniteResultsIsFalse :
      lacanOrIrigarayAreProofAuthorityForTheseFiniteResults ≡ false
    reading : String

canonicalEmbodiedSubjectModelInjectionBoundary : EmbodiedSubjectModelInjectionBoundary
canonicalEmbodiedSubjectModelInjectionBoundary =
  embodied-subject-model-injection-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Prompt, telemetry, role, memory and human-description inputs can modify an embodied agent's self-model without changing the underlying physical carrier or automatically changing moral-status evidence. Self-representation is not transparent subject access; constructed subjectivity is not thereby morally negligible; a model of another does not manufacture that other's consent. Lacanian/Irigarayan material is interpretive cross-pollination, not theorem authority."
