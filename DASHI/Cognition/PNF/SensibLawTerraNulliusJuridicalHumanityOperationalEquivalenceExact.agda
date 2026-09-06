module DASHI.Cognition.PNF.SensibLawTerraNulliusJuridicalHumanityOperationalEquivalenceExact where

------------------------------------------------------------------------
-- TERRA NULLIUS / JURIDICAL HUMANITY OPERATIONAL EQUIVALENCE
--
-- Source propositions remain Mabo/Brennan-owned only where the existing source
-- owner says they are direct. The equivalence below is SensibLaw's legal-
-- functional classification of the operative relation, not a fabricated quote.
--
-- The point is deliberately stronger than "dehumanising effect": for the
-- foundational acquisition / sovereignty / original-title relation, a legal
-- system that treats a physically present people with law, polity, occupancy
-- and proprietorship as if no legally constitutive people were present is, in
-- that relation, treating them as juridically non-human/non-persons.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Personhood
import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusJuridicalDehumanisationExact as Terra
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID

record JuridicalHumanityCriterion : Set where
  constructor juridical-humanity-criterion
  field
    relation : Personhood.FoundationalRelation
    physicalPeoplePresent : Bool
    lawAndPolityPresent : Bool
    occupancyAndProprietorshipPresent : Bool
    peopleCountAsConstitutiveLegalActors : Bool
    lawCountsAsConstitutive : Bool
    sovereigntyCountsAsConstitutive : Bool
    occupancyCountsAsFoundationalStanding : Bool
    proprietorshipCountsAgainstUnilateralTitle : Bool

open JuridicalHumanityCriterion public

terraNulliusCriterion : JuridicalHumanityCriterion
terraNulliusCriterion = juridical-humanity-criterion
  Personhood.crownAcquisitionRelation
  true true true
  false false false false false

data JuridicalHumanityOperationalState : Set where
  juridicallyHumanConstitutive
  juridicallyNonHumanNonconstitutive
  mixedOrUnresolved
  : JuridicalHumanityOperationalState

classify : JuridicalHumanityCriterion → JuridicalHumanityOperationalState
classify (juridical-humanity-criterion _ true true true false false false false false) =
  juridicallyNonHumanNonconstitutive
classify (juridical-humanity-criterion _ true true true true true true true true) =
  juridicallyHumanConstitutive
classify _ = mixedOrUnresolved

terraNulliusClassifiesAsJuridicallyNonHuman :
  classify terraNulliusCriterion ≡ juridicallyNonHumanNonconstitutive
terraNulliusClassifiesAsJuridicallyNonHuman = refl

existingPersonhoodStateIsErasedActor :
  Personhood.personhoodState Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ Personhood.juridicallyErasedActor
existingPersonhoodStateIsErasedActor = refl

existingJuridicalNonHumanityRegister :
  Personhood.register Personhood.terraNulliusRelationIndexedJuridicalNonHumanity
  ≡ Personhood.juridicalHumanity
existingJuridicalNonHumanityRegister = refl

existingSystemTreatedNoConstitutivePeopleAsPresent :
  Personhood.treatedAsIfNoJuridicallyConstitutivePeopleWerePresent
    Personhood.terraNulliusRelationIndexedJuridicalNonHumanity ≡ true
existingSystemTreatedNoConstitutivePeopleAsPresent = refl

record JuridicalNonHumanityReading : Set where
  constructor juridical-nonhumanity-reading
  field
    register : Personhood.HumanityRegister
    relation : Personhood.FoundationalRelation
    classification : JuridicalHumanityOperationalState
    classificationExact : classification ≡ juridicallyNonHumanNonconstitutive
    legallyConstitutiveHumanityDenied : Bool
    legallyConstitutiveHumanityDeniedIsTrue : legallyConstitutiveHumanityDenied ≡ true
    biologicalSpeciesClaimMade : Bool
    biologicalSpeciesClaimMadeIsFalse : biologicalSpeciesClaimMade ≡ false
    sourceQuotedUsingOurPhrase : Bool
    sourceQuotedUsingOurPhraseIsFalse : sourceQuotedUsingOurPhrase ≡ false
    reading : String

open JuridicalNonHumanityReading public

terraNulliusJuridicalNonHumanityReading : JuridicalNonHumanityReading
terraNulliusJuridicalNonHumanityReading = juridical-nonhumanity-reading
  Personhood.juridicalHumanity
  Personhood.crownAcquisitionRelation
  (classify terraNulliusCriterion) refl
  true refl
  false refl
  false refl
  "For the foundational Crown-acquisition/sovereignty/original-title relation, terra-nullius machinery treated physically present Indigenous peoples with actual law, polity, occupancy and proprietorship as if no legally constitutive people were present. In that legal register, this is juridical non-humanity/non-personhood, not merely a loose analogy. The source attribution remains narrower: Brennan records and rejects the discriminatory legal machinery; SensibLaw supplies this operational classification."

operationalBoundary : POSIWID.OperationalDescriptionBoundary
operationalBoundary = POSIWID.canonicalOperationalDescriptionBoundary

realizedOperationMayClassifySystem :
  POSIWID.observedOperationMayClassifyWhatSystemDoes operationalBoundary ≡ true
realizedOperationMayClassifySystem = refl

declaredPurposeCannotOverrideRepeatedLegalEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect operationalBoundary ≡ false
declaredPurposeCannotOverrideRepeatedLegalEffect = refl

privateIntentStillNotRequired :
  POSIWID.observedOperationProvesSubjectiveIntent operationalBoundary ≡ false
privateIntentStillNotRequired = refl

data JuridicalNonHumanityMeansBrennanSaidBiologicallyNonHuman : Set where
data OperationalClassificationIsOnlyMetaphor : Set where
data LaterMaboRejectionErasesPriorJuridicalNonHumanity : Set where

doesNotFabricateBiologicalBrennanQuote :
  JuridicalNonHumanityMeansBrennanSaidBiologicallyNonHuman → ⊥
doesNotFabricateBiologicalBrennanQuote ()

juridicalClassificationIsNotMerelyMetaphor :
  OperationalClassificationIsOnlyMetaphor → ⊥
juridicalClassificationIsNotMerelyMetaphor ()

laterRejectionDoesNotErasePriorOperation :
  LaterMaboRejectionErasesPriorJuridicalNonHumanity → ⊥
laterRejectionDoesNotErasePriorOperation ()

inhabitedCountryWasTreatedAsLegallyUninhabited :
  Terra.sourceSaysThisDirectly Terra.inhabitedTreatedAsDesertUninhabited ≡ true
inhabitedCountryWasTreatedAsLegallyUninhabited = refl

withoutLawWithoutSovereignWasDirectlyRecorded :
  Terra.sourceSaysThisDirectly Terra.withoutLawsWithoutSovereign ≡ true
withoutLawWithoutSovereignWasDirectlyRecorded = refl

discriminatoryDenigrationWasDirectlyRecorded :
  Terra.sourceSaysThisDirectly Terra.discriminatoryDenigrationBasis ≡ true
discriminatoryDenigrationWasDirectlyRecorded = refl
