module DASHI.Cognition.PNF.SensibLawMaboTerraNulliusTemporalLegalOperationExact where

------------------------------------------------------------------------
-- MABO / TERRA NULLIUS TEMPORAL LEGAL OPERATION
--
-- This owner corrects an important temporal category error: a doctrine can be
-- legally operative at t0 and later rejected at t1.  Later invalidation or
-- doctrinal correction does not mean the earlier rule never operated.
--
-- Primary-law calibration:
--   * Cooper v Stuart (1889) supplies the settled-colony classification surface.
--   * Mabo v Queensland (No 2) [1992] HCA 23 rejects the discriminatory common-
--     law consequence that denied Indigenous pre-existing land rights because
--     of the supposed social organisation of Indigenous peoples.
--
-- Mabo did not undo the historical acquisition/classification of sovereignty.
-- The settled-colony acquisition classification and the property/native-title
-- consequences drawn from it are therefore separately typed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.AuthorityBearingLegibilityFailureExact as Legibility
import DASHI.Governance.NormativeCorrectionMaterialPersistenceExact as Persistence

------------------------------------------------------------------------
-- Time and legal coordinates.
------------------------------------------------------------------------

data LegalTemporalStage : Set where
  preMaboOrthodoxRegime
  mabo1992Correction
  postMaboRecognitionRegime
  : LegalTemporalStage

data SettledColonyClassification : Set where
  settledClassificationOperative : SettledColonyClassification

data PropertyConsequence : Set where
  crownBeneficialOwnershipExhaustive
  radicalTitleCompatibleWithNativeTitle
  : PropertyConsequence

data NativeTitleVisibility : Set where
  nativeTitleDeniedByOrthodoxRule
  nativeTitleRecognisableAtCommonLaw
  : NativeTitleVisibility

data DoctrinalEvaluation : Set where
  discriminatoryDenigrationOperative
  discriminatoryDoctrineRejected
  : DoctrinalEvaluation

settledClassification : LegalTemporalStage → SettledColonyClassification
settledClassification preMaboOrthodoxRegime = settledClassificationOperative
settledClassification mabo1992Correction = settledClassificationOperative
settledClassification postMaboRecognitionRegime = settledClassificationOperative

propertyConsequence : LegalTemporalStage → PropertyConsequence
propertyConsequence preMaboOrthodoxRegime = crownBeneficialOwnershipExhaustive
propertyConsequence mabo1992Correction = radicalTitleCompatibleWithNativeTitle
propertyConsequence postMaboRecognitionRegime = radicalTitleCompatibleWithNativeTitle

nativeTitleVisibility : LegalTemporalStage → NativeTitleVisibility
nativeTitleVisibility preMaboOrthodoxRegime = nativeTitleDeniedByOrthodoxRule
nativeTitleVisibility mabo1992Correction = nativeTitleRecognisableAtCommonLaw
nativeTitleVisibility postMaboRecognitionRegime = nativeTitleRecognisableAtCommonLaw

doctrinalEvaluation : LegalTemporalStage → DoctrinalEvaluation
doctrinalEvaluation preMaboOrthodoxRegime = discriminatoryDenigrationOperative
doctrinalEvaluation mabo1992Correction = discriminatoryDoctrineRejected
doctrinalEvaluation postMaboRecognitionRegime = discriminatoryDoctrineRejected

preMaboPropertyConsequenceWasOperative :
  propertyConsequence preMaboOrthodoxRegime ≡ crownBeneficialOwnershipExhaustive
preMaboPropertyConsequenceWasOperative = refl

preMaboNativeTitleWasDeniedByOrthodoxRule :
  nativeTitleVisibility preMaboOrthodoxRegime ≡ nativeTitleDeniedByOrthodoxRule
preMaboNativeTitleWasDeniedByOrthodoxRule = refl

maboRejectsThePropertyConsequence :
  propertyConsequence mabo1992Correction ≡ radicalTitleCompatibleWithNativeTitle
maboRejectsThePropertyConsequence = refl

maboMakesNativeTitleRecognisableAtCommonLaw :
  nativeTitleVisibility mabo1992Correction ≡ nativeTitleRecognisableAtCommonLaw
maboMakesNativeTitleRecognisableAtCommonLaw = refl

settledClassificationIsNotTheCorrectedCoordinate :
  settledClassification preMaboOrthodoxRegime ≡
  settledClassification mabo1992Correction
settledClassificationIsNotTheCorrectedCoordinate = refl

------------------------------------------------------------------------
-- Historical legal operation != current validity != legitimacy.
------------------------------------------------------------------------

record TemporalLegalOperationReceipt : Set where
  constructor temporal-legal-operation-receipt
  field
    sourceReference : String
    historicalRuleOperated : Bool
    historicalRuleOperatedIsTrue : historicalRuleOperated ≡ true
    laterCourtRejectedRuleOrConsequence : Bool
    laterCourtRejectedRuleOrConsequenceIsTrue : laterCourtRejectedRuleOrConsequence ≡ true
    laterRejectionMeansEarlierRuleNeverOperated : Bool
    laterRejectionMeansEarlierRuleNeverOperatedIsFalse :
      laterRejectionMeansEarlierRuleNeverOperated ≡ false
    historicalLegalOperationProvesMoralLegitimacy : Bool
    historicalLegalOperationProvesMoralLegitimacyIsFalse :
      historicalLegalOperationProvesMoralLegitimacy ≡ false
    historicalLegalOperationProvesOntologicalTruth : Bool
    historicalLegalOperationProvesOntologicalTruthIsFalse :
      historicalLegalOperationProvesOntologicalTruth ≡ false

open TemporalLegalOperationReceipt public

canonicalTerraNulliusTemporalReceipt : TemporalLegalOperationReceipt
canonicalTerraNulliusTemporalReceipt = temporal-legal-operation-receipt
  "Cooper v Stuart (1889) 14 App Cas 286; Mabo v Queensland (No 2) [1992] HCA 23"
  true refl
  true refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- The discriminatory basis is not softened out of the legal history.
------------------------------------------------------------------------

record DiscriminatoryDoctrineReceipt : Set where
  constructor discriminatory-doctrine-receipt
  field
    propositionReference : String
    sourceKind : String
    sourceDirectlyCharacterisesPriorDoctrineAsDiscriminatory : Bool
    sourceDirectlyCharacterisesPriorDoctrineAsDiscriminatoryIsTrue :
      sourceDirectlyCharacterisesPriorDoctrineAsDiscriminatory ≡ true
    priorDoctrineHadLegalConsequences : Bool
    priorDoctrineHadLegalConsequencesIsTrue : priorDoctrineHadLegalConsequences ≡ true
    criticalDehumanisationReadingIsSeparateInterpretation : Bool
    criticalDehumanisationReadingIsSeparateInterpretationIsTrue :
      criticalDehumanisationReadingIsSeparateInterpretation ≡ true
    courtLiterallyHeldIndigenousPeopleWereNonHuman : Bool
    courtLiterallyHeldIndigenousPeopleWereNonHumanIsFalse :
      courtLiterallyHeldIndigenousPeopleWereNonHuman ≡ false

open DiscriminatoryDoctrineReceipt public

canonicalDiscriminatoryDoctrineReceipt : DiscriminatoryDoctrineReceipt
canonicalDiscriminatoryDoctrineReceipt = discriminatory-doctrine-receipt
  "Brennan J: prior denial of Indigenous land rights depended on discriminatory denigration / supposed social-organisation hierarchy and the unjust discriminatory doctrine could no longer be accepted"
  "Mabo (No 2) primary judicial reasoning"
  true refl
  true refl
  true refl
  false refl

------------------------------------------------------------------------
-- Critical/decolonial interpretation: juridical ontological dehumanisation.
--
-- This describes what the operative colonial legal chart DID: Indigenous law,
-- polity and land relations could exist in the social world while the dominant
-- legal representation treated them as absent for rights-bearing purposes.
-- It is not back-attributed as Brennan's literal proposition about humanity.
------------------------------------------------------------------------

data InterpretationAuthority : Set where
  primaryCourtHolding
  criticalDecolonialInterpretation
  repositoryStructuralTheorem
  : InterpretationAuthority

record JuridicalOntologicalDehumanisationInterpretation : Set where
  constructor juridical-ontological-dehumanisation-interpretation
  field
    interpretationAuthority : InterpretationAuthority
    reading : String
    usesAuthorityBearingLegibilityWitness : Bool
    usesAuthorityBearingLegibilityWitnessIsTrue :
      usesAuthorityBearingLegibilityWitness ≡ true
    claimsLiteralNonHumanHolding : Bool
    claimsLiteralNonHumanHoldingIsFalse : claimsLiteralNonHumanHolding ≡ false
    claimsPriorDoctrineWasLegallyInoperative : Bool
    claimsPriorDoctrineWasLegallyInoperativeIsFalse :
      claimsPriorDoctrineWasLegallyInoperative ≡ false

open JuridicalOntologicalDehumanisationInterpretation public

canonicalJuridicalDehumanisationInterpretation :
  JuridicalOntologicalDehumanisationInterpretation
canonicalJuridicalDehumanisationInterpretation =
  juridical-ontological-dehumanisation-interpretation
    criticalDecolonialInterpretation
    "Critical/decolonial reading: the operative colonial legal chart functioned as juridical/ontological dehumanisation by rendering Indigenous law, polity and Country relations non-legible or non-right-bearing to the dominant legal order despite their social existence."
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing authority-bearing legibility and material-persistence owners weld in.
------------------------------------------------------------------------

historicalLegibilityFailureRemainsConstructed : Legibility.LegibilityFailure
historicalLegibilityFailureRemainsConstructed = Legibility.canonicalLegibilityFailure

lossyRepresentationFedInstitutionalAction :
  Legibility.lossyRepresentationCanFeedInstitutionalAction
    Legibility.canonicalAuthorityBearingLegibilityBoundary ≡ true
lossyRepresentationFedInstitutionalAction = refl

maboCorrectionDoesNotEqualCompleteMaterialRepair :
  Persistence.legalCorrectionEqualsCompleteRepair
    Persistence.canonicalNormativeCorrectionMaterialPersistenceBoundary ≡ false
maboCorrectionDoesNotEqualCompleteMaterialRepair = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data LaterRejectionMeansEarlierRuleNeverOperated : Set where
data LegalValidityMeansMoralLegitimacy : Set where
data SettledClassificationMeansNoIndigenousLawExists : Set where
data MaboRejectedAcquisitionOfSovereignty : Set where
data CriticalDehumanisationReadingIsLiteralMaboHolding : Set where
data MaboCorrectionRetroactivelyErasesMaterialConsequences : Set where

laterRejectionDoesNotEraseHistoricalOperation :
  LaterRejectionMeansEarlierRuleNeverOperated → ⊥
laterRejectionDoesNotEraseHistoricalOperation ()

legalValidityDoesNotConferMoralLegitimacy : LegalValidityMeansMoralLegitimacy → ⊥
legalValidityDoesNotConferMoralLegitimacy ()

settledClassificationDoesNotProveIndigenousLawAbsent :
  SettledClassificationMeansNoIndigenousLawExists → ⊥
settledClassificationDoesNotProveIndigenousLawAbsent ()

maboDidNotJudiciallyUndoSovereigntyAcquisition : MaboRejectedAcquisitionOfSovereignty → ⊥
maboDidNotJudiciallyUndoSovereigntyAcquisition ()

criticalReadingDoesNotBecomeLiteralHolding :
  CriticalDehumanisationReadingIsLiteralMaboHolding → ⊥
criticalReadingDoesNotBecomeLiteralHolding ()

maboCorrectionDoesNotRetroactivelyEraseConsequences :
  MaboCorrectionRetroactivelyErasesMaterialConsequences → ⊥
maboCorrectionDoesNotRetroactivelyEraseConsequences ()

record TerraNulliusTemporalBoundary : Set where
  constructor terra-nullius-temporal-boundary
  field
    preMaboDoctrineLegallyOperative : Bool
    preMaboDoctrineLegallyOperativeIsTrue : preMaboDoctrineLegallyOperative ≡ true
    discriminatoryBasisPartOfDoctrinalHistory : Bool
    discriminatoryBasisPartOfDoctrinalHistoryIsTrue :
      discriminatoryBasisPartOfDoctrinalHistory ≡ true
    maboChangedCommonLawLandRightsConsequences : Bool
    maboChangedCommonLawLandRightsConsequencesIsTrue :
      maboChangedCommonLawLandRightsConsequences ≡ true
    maboErasedSettledClassification : Bool
    maboErasedSettledClassificationIsFalse : maboErasedSettledClassification ≡ false
    maboErasedHistoricalMaterialEffects : Bool
    maboErasedHistoricalMaterialEffectsIsFalse : maboErasedHistoricalMaterialEffects ≡ false

open TerraNulliusTemporalBoundary public

canonicalTerraNulliusTemporalBoundary : TerraNulliusTemporalBoundary
canonicalTerraNulliusTemporalBoundary = terra-nullius-temporal-boundary
  true refl
  true refl
  true refl
  false refl
  false refl
