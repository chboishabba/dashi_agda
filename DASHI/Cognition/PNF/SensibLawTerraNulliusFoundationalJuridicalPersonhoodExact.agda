module DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact where

------------------------------------------------------------------------
-- TERRA NULLIUS / FOUNDATIONAL JURIDICAL PERSONHOOD
--
-- This owner strengthens the operative classification already present in
-- SensibLawMaboTerraNulliusJuridicalDehumanisationExact.
--
-- Source propositions remain Brennan J / Mabo-owned where directly attributed.
-- The relation-indexed classifications below are SensibLaw/DASHI constructions.
-- They do not back-attribute our vocabulary to Brennan J.
--
-- The relevant relation is deliberately narrow and foundational:
-- Crown acquisition / sovereignty / original land-title constitutivity.
-- A physically present people with law, polity, occupancy and proprietorship
-- can be treated as juridically absent/non-constitutive in that relation even
-- though the same legal order may recognise them for other purposes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusJuridicalDehumanisationExact as Terra
import DASHI.Governance.AuthorityBearingLegibilityFailureExact as Legibility
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID

------------------------------------------------------------------------
-- Relation-indexed juridical standing.
------------------------------------------------------------------------

data FoundationalRelation : Set where
  crownAcquisitionRelation : FoundationalRelation
  sovereigntyConstitutivityRelation : FoundationalRelation
  originalLandTitleRelation : FoundationalRelation


data JuridicalPersonhoodState : Set where
  constitutiveJuridicalActor : JuridicalPersonhoodState
  juridicallyPresentButNonconstitutive : JuridicalPersonhoodState
  juridicallyErasedActor : JuridicalPersonhoodState


record RelationIndexedJuridicalPersonhood : Set where
  constructor relation-indexed-juridical-personhood
  field
    relation : FoundationalRelation
    physicallyPresent : Bool
    physicallyPresentIsTrue : physicallyPresent ≡ true
    lawActuallyPresent : Bool
    lawActuallyPresentIsTrue : lawActuallyPresent ≡ true
    polityActuallyPresent : Bool
    polityActuallyPresentIsTrue : polityActuallyPresent ≡ true
    occupancyActuallyPresent : Bool
    occupancyActuallyPresentIsTrue : occupancyActuallyPresent ≡ true
    lawCountsAgainstUnilateralAcquisition : Bool
    lawCountsAgainstUnilateralAcquisitionIsFalse :
      lawCountsAgainstUnilateralAcquisition ≡ false
    sovereigntyCountsAgainstUnilateralAcquisition : Bool
    sovereigntyCountsAgainstUnilateralAcquisitionIsFalse :
      sovereigntyCountsAgainstUnilateralAcquisition ≡ false
    occupancyCountsAsFoundationalProprietaryStanding : Bool
    occupancyCountsAsFoundationalProprietaryStandingIsFalse :
      occupancyCountsAsFoundationalProprietaryStanding ≡ false
    proprietorshipCountsAgainstCrownTitleDerivation : Bool
    proprietorshipCountsAgainstCrownTitleDerivationIsFalse :
      proprietorshipCountsAgainstCrownTitleDerivation ≡ false
    personhoodState : JuridicalPersonhoodState
    personhoodStateExact : personhoodState ≡ juridicallyErasedActor
    sourcePhraseClaimsBiologicalNonHumanity : Bool
    sourcePhraseClaimsBiologicalNonHumanityIsFalse :
      sourcePhraseClaimsBiologicalNonHumanity ≡ false
    classificationReference : String

open RelationIndexedJuridicalPersonhood public

terraNulliusFoundationalJuridicalPersonhood : RelationIndexedJuridicalPersonhood
terraNulliusFoundationalJuridicalPersonhood = relation-indexed-juridical-personhood
  crownAcquisitionRelation
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  juridicallyErasedActor refl
  false refl
  "SensibLaw relation-indexed classification: for the foundational Crown-acquisition/land-sovereignty relation, physically present Indigenous peoples with actual law, polity, occupancy and proprietary relations were treated as non-constitutive juridical actors when the legal machinery posited unilateral Crown acquisition/title."

------------------------------------------------------------------------
-- Stronger interpretation: juridical humanity/personhood is not biologicality.
------------------------------------------------------------------------

data HumanityRegister : Set where
  biologicalHumanity : HumanityRegister
  socialHumanity : HumanityRegister
  juridicalHumanity : HumanityRegister
  politicalConstitutiveStanding : HumanityRegister


record RelationIndexedJuridicalNonHumanity : Set where
  constructor relation-indexed-juridical-nonhumanity
  field
    register : HumanityRegister
    relation : FoundationalRelation
    physicalHumanPresenceDenied : Bool
    physicalHumanPresenceDeniedIsFalse : physicalHumanPresenceDenied ≡ false
    humanLawPolityRelationDeniedConstitutiveForce : Bool
    humanLawPolityRelationDeniedConstitutiveForceIsTrue :
      humanLawPolityRelationDeniedConstitutiveForce ≡ true
    treatedAsIfNoJuridicallyConstitutivePeopleWerePresent : Bool
    treatedAsIfNoJuridicallyConstitutivePeopleWerePresentIsTrue :
      treatedAsIfNoJuridicallyConstitutivePeopleWerePresent ≡ true
    classificationIsLegalFunctional : Bool
    classificationIsLegalFunctionalIsTrue : classificationIsLegalFunctional ≡ true
    classificationIsBiologicalTaxonomy : Bool
    classificationIsBiologicalTaxonomyIsFalse : classificationIsBiologicalTaxonomy ≡ false
    classificationReading : String

open RelationIndexedJuridicalNonHumanity public

terraNulliusRelationIndexedJuridicalNonHumanity : RelationIndexedJuridicalNonHumanity
terraNulliusRelationIndexedJuridicalNonHumanity = relation-indexed-juridical-nonhumanity
  juridicalHumanity
  crownAcquisitionRelation
  false refl
  true refl
  true refl
  true refl
  false refl
  "Within the foundational land-sovereignty relation, the system treated Indigenous peoples as if no legally constitutive law-bearing, sovereign, occupying or proprietary people were present. SensibLaw therefore classifies the operation as relation-indexed juridical non-humanity/non-personhood. This is an operative legal classification, not a biological quotation attributed to Brennan J."

------------------------------------------------------------------------
-- This is not just rhetoric: it is inherited from the exact capacity denials.
------------------------------------------------------------------------

peopleWerePhysicallyPresent :
  Terra.peoplePhysicallyPresent Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
peopleWerePhysicallyPresent = refl

lawAndSocialOrderWerePresent :
  Terra.lawSocialOrderActuallyPresent Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
lawAndSocialOrderWerePresent = refl

systemTreatedCountryAsLegallyUninhabited :
  Terra.treatedAsLegallyUninhabited Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
systemTreatedCountryAsLegallyUninhabited = refl

systemDeniedLawConstitutiveStanding :
  Terra.localLawDeniedConstitutiveStanding Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
systemDeniedLawConstitutiveStanding = refl

systemDeniedSovereigntyConstitutiveStanding :
  Terra.indigenousSovereigntyDeniedConstitutiveStanding
    Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
systemDeniedSovereigntyConstitutiveStanding = refl

systemDeniedOccupancyProprietaryStanding :
  Terra.occupancyDeniedProprietaryStanding Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
systemDeniedOccupancyProprietaryStanding = refl

systemActedOnProjection :
  Terra.institutionalActionFollowedProjection Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
systemActedOnProjection = refl

------------------------------------------------------------------------
-- POSIWID cross-pollination: operative legal treatment is itself evidence of
-- what the legal machinery did, independent of a charitable mission statement.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

operationMayClassifyWhatSystemDoes :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
operationMayClassifyWhatSystemDoes = refl

declaredPurposeDoesNotOverrideRepeatedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRepeatedEffect = refl

operationDoesNotByItselfProvePrivateIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationDoesNotByItselfProvePrivateIntent = refl

------------------------------------------------------------------------
-- Authority-bearing legibility failure remains the same-object structural base.
------------------------------------------------------------------------

actualWorldLawPresent :
  Legibility.SocialWorld.lawPresent Legibility.indigenousWorldWitness ≡ true
actualWorldLawPresent = refl

actualWorldPolityPresent :
  Legibility.SocialWorld.polityPresent Legibility.indigenousWorldWitness ≡ true
actualWorldPolityPresent = refl

authorityRepresentationRecognisesNoLaw :
  Legibility.AuthorityRepresentation.recognisesLaw
    Legibility.settledColonyRepresentationWitness ≡ false
authorityRepresentationRecognisesNoLaw = refl

authorityRepresentationRecognisesNoPolity :
  Legibility.AuthorityRepresentation.recognisesPolity
    Legibility.settledColonyRepresentationWitness ≡ false
authorityRepresentationRecognisesNoPolity = refl

------------------------------------------------------------------------
-- No-collapse / scope boundaries.
------------------------------------------------------------------------

data RelationIndexedNonPersonhoodMeansNoLegalRecognitionAnywhere : Set where
data RelationIndexedJuridicalNonHumanityIsBiologicalNonHumanity : Set where
data BrennanUsedRelationIndexedJuridicalNonHumanityPhrase : Set where
data MaboRejectionRetroactivelyErasesPriorOperation : Set where
data OperativeClassificationRequiresRacialHatredFinding : Set where

relationIndexedDoesNotMeanNoRecognitionAnywhere :
  RelationIndexedNonPersonhoodMeansNoLegalRecognitionAnywhere → ⊥
relationIndexedDoesNotMeanNoRecognitionAnywhere ()

juridicalNonHumanityIsNotBiologicalTaxonomy :
  RelationIndexedJuridicalNonHumanityIsBiologicalNonHumanity → ⊥
juridicalNonHumanityIsNotBiologicalTaxonomy ()

ourClassificationDoesNotBackTransferToBrennan :
  BrennanUsedRelationIndexedJuridicalNonHumanityPhrase → ⊥
ourClassificationDoesNotBackTransferToBrennan ()

laterRejectionDoesNotErasePriorOperation :
  MaboRejectionRetroactivelyErasesPriorOperation → ⊥
laterRejectionDoesNotErasePriorOperation ()

operativeClassificationDoesNotRequirePrivateHatred :
  OperativeClassificationRequiresRacialHatredFinding → ⊥
operativeClassificationDoesNotRequirePrivateHatred ()
