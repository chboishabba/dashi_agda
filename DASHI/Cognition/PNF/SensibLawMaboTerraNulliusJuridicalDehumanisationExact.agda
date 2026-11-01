module DASHI.Cognition.PNF.SensibLawMaboTerraNulliusJuridicalDehumanisationExact where

------------------------------------------------------------------------
-- TERRA NULLIUS / FUNCTIONAL JURIDICAL DEHUMANISATION
--
-- Source boundary:
--   Mabo v Queensland (No 2) [1992] HCA 23, Brennan J.
--
-- Brennan's reasoning records that the enlarged settled-colony hypothesis
-- could treat inhabited territory as legally "desert uninhabited"; that the
-- Indigenous inhabitants were taken to be without laws and without a sovereign;
-- that their occupancy was ignored in deriving Crown ownership; and that the
-- theory depended on discriminatory denigration of Indigenous social
-- organisation and customs.
--
-- The phrase "functional juridical dehumanisation" below is DASHI/SensibLaw's
-- legal-functional classification of what that machinery did.  It is not
-- back-attributed as a phrase used by Brennan J and it is not a claim that the
-- judgment contains the biological proposition "Indigenous people are
-- non-human".
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.AuthorityBearingLegibilityFailureExact as Legibility
import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized

------------------------------------------------------------------------
-- Foundational juridical standing is coordinate-specific.
------------------------------------------------------------------------

data FoundationalJuridicalCapacity : Set where
  suppliesLegalOccupancy : FoundationalJuridicalCapacity
  suppliesLocalLaw : FoundationalJuridicalCapacity
  suppliesPoliticalSovereignty : FoundationalJuridicalCapacity
  suppliesLandProprietorship : FoundationalJuridicalCapacity


data RecognitionState : Set where
  recognisedCapacity : RecognitionState
  deniedCapacity : RecognitionState

data TerraNulliusOperation : Set where
  treatInhabitedAsLegallyUninhabited : TerraNulliusOperation
  denyLocalLawAsJuridicallyConstitutive : TerraNulliusOperation
  denyIndigenousSovereignAsJuridicallyConstitutive : TerraNulliusOperation
  ignoreIndigenousOccupancyForCrownTitle : TerraNulliusOperation
  ignoreIndigenousProprietorshipForCrownTitle : TerraNulliusOperation


record MaboPrimaryProposition : Set where
  constructor mabo-primary-proposition
  field
    propositionReference : String
    sourceReference : String
    sourceSpeaker : String
    sourceSaysThisDirectly : Bool
    interpretiveExtension : Bool

open MaboPrimaryProposition public

inhabitedTreatedAsDesertUninhabited : MaboPrimaryProposition
inhabitedTreatedAsDesertUninhabited = mabo-primary-proposition
  "For municipal-law purposes, inhabited territory could be treated under the enlarged terra-nullius hypothesis as desert uninhabited country."
  "Mabo v Queensland (No 2) [1992] HCA 23, Brennan J, discussion of settled colonies / enlarged terra nullius"
  "Brennan J"
  true false

withoutLawsWithoutSovereign : MaboPrimaryProposition
withoutLawsWithoutSovereign = mabo-primary-proposition
  "Under the settled-colony hypothesis, Indigenous inhabitants were taken to be without laws, without a sovereign, and primitive in social organisation."
  "Mabo v Queensland (No 2) [1992] HCA 23, Brennan J"
  "Brennan J"
  true false

occupancyIgnoredForTitle : MaboPrimaryProposition
occupancyIgnoredForTitle = mabo-primary-proposition
  "Indigenous inhabitants and their occupancy were ignored when title to land in a settled colony was considered, enabling Crown ownership to be posited because there was said to be no other proprietor."
  "Mabo v Queensland (No 2) [1992] HCA 23, Brennan J"
  "Brennan J"
  true false

discriminatoryDenigrationBasis : MaboPrimaryProposition
discriminatoryDenigrationBasis = mabo-primary-proposition
  "The theory that Indigenous inhabitants of a settled colony had no proprietary interest depended on discriminatory denigration of Indigenous inhabitants, their social organisation and customs."
  "Mabo v Queensland (No 2) [1992] HCA 23, Brennan J"
  "Brennan J"
  true false

------------------------------------------------------------------------
-- Functional juridical dehumanisation is defined by operative capacity denial.
------------------------------------------------------------------------

record FunctionalJuridicalDehumanisation : Set where
  constructor functional-juridical-dehumanisation
  field
    peoplePhysicallyPresent : Bool
    peoplePhysicallyPresentIsTrue : peoplePhysicallyPresent ≡ true
    lawSocialOrderActuallyPresent : Bool
    lawSocialOrderActuallyPresentIsTrue : lawSocialOrderActuallyPresent ≡ true
    treatedAsLegallyUninhabited : Bool
    treatedAsLegallyUninhabitedIsTrue : treatedAsLegallyUninhabited ≡ true
    localLawDeniedConstitutiveStanding : Bool
    localLawDeniedConstitutiveStandingIsTrue : localLawDeniedConstitutiveStanding ≡ true
    indigenousSovereigntyDeniedConstitutiveStanding : Bool
    indigenousSovereigntyDeniedConstitutiveStandingIsTrue :
      indigenousSovereigntyDeniedConstitutiveStanding ≡ true
    occupancyDeniedProprietaryStanding : Bool
    occupancyDeniedProprietaryStandingIsTrue : occupancyDeniedProprietaryStanding ≡ true
    institutionalActionFollowedProjection : Bool
    institutionalActionFollowedProjectionIsTrue : institutionalActionFollowedProjection ≡ true
    biologicalNonHumanPropositionRequired : Bool
    biologicalNonHumanPropositionRequiredIsFalse : biologicalNonHumanPropositionRequired ≡ false
    classificationReference : String

open FunctionalJuridicalDehumanisation public

terraNulliusFunctionalJuridicalDehumanisation : FunctionalJuridicalDehumanisation
terraNulliusFunctionalJuridicalDehumanisation = functional-juridical-dehumanisation
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  false refl
  "Functional legal classification: inhabited Indigenous political communities were denied the law/sovereignty/occupancy/proprietorship capacities by which they could count against unilateral Crown acquisition in the foundational land-sovereignty relation."

------------------------------------------------------------------------
-- Reuse existing exact legibility witness rather than duplicating it.
------------------------------------------------------------------------

terraNulliusWorldHasLaw :
  Legibility.SocialWorld.lawPresent Legibility.indigenousWorldWitness ≡ true
terraNulliusWorldHasLaw = refl

terraNulliusWorldHasPolity :
  Legibility.SocialWorld.polityPresent Legibility.indigenousWorldWitness ≡ true
terraNulliusWorldHasPolity = refl

settledColonyRepresentationRecognisesNoLaw :
  Legibility.AuthorityRepresentation.recognisesLaw
    Legibility.settledColonyRepresentationWitness ≡ false
settledColonyRepresentationRecognisesNoLaw = refl

settledColonyRepresentationRecognisesNoPolity :
  Legibility.AuthorityRepresentation.recognisesPolity
    Legibility.settledColonyRepresentationWitness ≡ false
settledColonyRepresentationRecognisesNoPolity = refl

settledColonyRepresentationRecognisesNoLandRelation :
  Legibility.AuthorityRepresentation.recognisesLandRelations
    Legibility.settledColonyRepresentationWitness ≡ false
settledColonyRepresentationRecognisesNoLandRelation = refl

------------------------------------------------------------------------
-- "A system is what it does": realised operation != declared anthropology.
------------------------------------------------------------------------

record FunctionalSystemReading : Set where
  constructor functional-system-reading
  field
    systemReference : String
    declaredBiologicalAnthropology : String
    realisedLegalOperation : String
    operationCanBeClassifiedFromEffects : Bool
    operationCanBeClassifiedFromEffectsIsTrue : operationCanBeClassifiedFromEffects ≡ true
    effectClassificationEqualsSpeakerQuotation : Bool
    effectClassificationEqualsSpeakerQuotationIsFalse :
      effectClassificationEqualsSpeakerQuotation ≡ false
    effectClassificationProvesPrivateMotive : Bool
    effectClassificationProvesPrivateMotiveIsFalse :
      effectClassificationProvesPrivateMotive ≡ false

open FunctionalSystemReading public

terraNulliusSystemReading : FunctionalSystemReading
terraNulliusSystemReading = functional-system-reading
  "enlarged terra-nullius / settled-colony land-sovereignty machinery"
  "No proposition is attributed to Brennan J that Indigenous people were biologically non-human."
  "The machinery treated an inhabited Indigenous political/legal order as legally uninhabited and non-constitutive for sovereignty, law, occupancy and proprietorship in the foundational acquisition relation."
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Operative discrimination can be stronger than explicit discriminatory words.
------------------------------------------------------------------------

record OperativeDiscriminationBoundary : Set where
  constructor operative-discrimination-boundary
  field
    explicitSlurRequiredForDiscriminatoryLegalOperation : Bool
    explicitSlurRequiredForDiscriminatoryLegalOperationIsFalse :
      explicitSlurRequiredForDiscriminatoryLegalOperation ≡ false
    legalOperativenessCompatibleWithDiscriminatoryEffect : Bool
    legalOperativenessCompatibleWithDiscriminatoryEffectIsTrue :
      legalOperativenessCompatibleWithDiscriminatoryEffect ≡ true
    judicialRejectionErasesPriorMaterialConsequences : Bool
    judicialRejectionErasesPriorMaterialConsequencesIsFalse :
      judicialRejectionErasesPriorMaterialConsequences ≡ false
    explicitBiologicalNonHumanHoldingAttributedToBrennan : Bool
    explicitBiologicalNonHumanHoldingAttributedToBrennanIsFalse :
      explicitBiologicalNonHumanHoldingAttributedToBrennan ≡ false
    functionalJuridicalDehumanisationClassificationAvailable : Bool
    functionalJuridicalDehumanisationClassificationAvailableIsTrue :
      functionalJuridicalDehumanisationClassificationAvailable ≡ true

canonicalOperativeDiscriminationBoundary : OperativeDiscriminationBoundary
canonicalOperativeDiscriminationBoundary = operative-discrimination-boundary
  false refl
  true refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data FunctionalJuridicalDehumanisationMeansBiologicalNonHumanHolding : Set where
data BrennanUsedOurFunctionalDehumanisationPhrase : Set where
data DiscriminatoryOperationRequiresProvenPrivateHatred : Set where
data MaboCorrectionCompletedMaterialReparation : Set where

functionalLegalClassificationDoesNotBecomeBiologicalHolding :
  FunctionalJuridicalDehumanisationMeansBiologicalNonHumanHolding → ⊥
functionalLegalClassificationDoesNotBecomeBiologicalHolding ()

ourPhraseDoesNotTransferToBrennan : BrennanUsedOurFunctionalDehumanisationPhrase → ⊥
ourPhraseDoesNotTransferToBrennan ()

discriminatoryOperationDoesNotRequirePrivateHatredProof :
  DiscriminatoryOperationRequiresProvenPrivateHatred → ⊥
discriminatoryOperationDoesNotRequirePrivateHatredProof ()

maboCorrectionDidNotCompleteReparation : MaboCorrectionCompletedMaterialReparation → ⊥
maboCorrectionDidNotCompleteReparation ()
