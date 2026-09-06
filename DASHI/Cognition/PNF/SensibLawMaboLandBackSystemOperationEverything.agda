module DASHI.Cognition.PNF.SensibLawMaboLandBackSystemOperationEverything where

------------------------------------------------------------------------
-- PREFERRED SYSTEM-OPERATION CAPSTONE
--
-- Extends the epistemic-compression capstone with temporal legal operation,
-- visibility/existence noncollapse, POSIWID-calibrated operational semantics,
-- self-sealing correction loops and forum/enforcement separation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawMaboLandBackEpistemicCompressionEverything as Previous
import DASHI.Cognition.PNF.SensibLawSystemOperationProjectionEnforcementCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusTemporalLegalOperationExact as Terra
import DASHI.Cognition.PNF.SensibLawClimateForumCompulsionEnforcementLatticeExact as Climate
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as Operation
import DASHI.Core.ObserverVisibilityExistenceNoncollapseExact as Visibility
import DASHI.Core.SelfSealingCorrectionLoopExact as SelfSeal
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression

------------------------------------------------------------------------
-- Prior Country / anti-commodity-form boundary remains canonical.
------------------------------------------------------------------------

countryIsNotAssetOntology :
  Previous.countryRelationIsNotAssetByDefault
  ≡ Previous.countryRelationIsNotAssetByDefault
countryIsNotAssetOntology = refl

commodityFormIsNotNeutralUniversalOntology :
  Previous.commodityFormIsNotUniversalNeutralOntology
  ≡ Previous.commodityFormIsNotUniversalNeutralOntology
commodityFormIsNotNeutralUniversalOntology = refl

------------------------------------------------------------------------
-- Visibility/existence theorem now has a preferred downstream export.
------------------------------------------------------------------------

invisibleToObserverDoesNotMeanNonexistent : Visibility.InvisibleMeansNonexistent → ⊥
invisibleToObserverDoesNotMeanNonexistent = Cross.invisibleDoesNotMeanNonexistent

institutionalVisibilityDoesNotConstituteExistence :
  Cross.recognitionDoesNotConstituteExistence
  ≡ Cross.recognitionDoesNotConstituteExistence
institutionalVisibilityDoesNotConstituteExistence = refl

------------------------------------------------------------------------
-- A system is what it does: declared purpose and operation stay separated.
------------------------------------------------------------------------

posiwidSourceBoundary : Operation.POSIWIDSourceBoundary
posiwidSourceBoundary = Cross.posiwidBoundary

declaredMissionDoesNotDetermineRealizedEffect :
  Operation.MissionStatementDeterminesSystemEffect → ⊥
declaredMissionDoesNotDetermineRealizedEffect = Cross.missionStatementCannotDetermineEffect

observedOperationDoesNotProveIntent :
  Operation.observedOperationProvesSubjectiveIntent
    Operation.canonicalOperationalDescriptionBoundary ≡ false
observedOperationDoesNotProveIntent = refl

correctionHandlingIsObservableOperation :
  Operation.correctionResponseIsPartOfObservableOperation
    Operation.canonicalOperationalDescriptionBoundary ≡ true
correctionHandlingIsObservableOperation = refl

------------------------------------------------------------------------
-- Terra-nullius temporal legal operation: no retroactive sanitisation.
------------------------------------------------------------------------

preMaboDoctrineOperatedInLaw :
  Terra.preMaboDoctrineLegallyOperative Terra.canonicalTerraNulliusTemporalBoundary ≡ true
preMaboDoctrineOperatedInLaw = refl

preMaboDiscriminatoryBasisRemainsPartOfLegalHistory :
  Terra.discriminatoryBasisPartOfDoctrinalHistory Terra.canonicalTerraNulliusTemporalBoundary ≡ true
preMaboDiscriminatoryBasisRemainsPartOfLegalHistory = refl

maboChangedCommonLawLandRightsConsequences :
  Terra.maboChangedCommonLawLandRightsConsequences Terra.canonicalTerraNulliusTemporalBoundary ≡ true
maboChangedCommonLawLandRightsConsequences = refl

maboDidNotRetroactivelyMakePriorRuleInoperative :
  Terra.LaterRejectionMeansEarlierRuleNeverOperated → ⊥
maboDidNotRetroactivelyMakePriorRuleInoperative =
  Terra.laterRejectionDoesNotEraseHistoricalOperation

historicalLegalValidityDoesNotEqualMoralLegitimacy :
  Terra.LegalValidityMeansMoralLegitimacy → ⊥
historicalLegalValidityDoesNotEqualMoralLegitimacy =
  Terra.legalValidityDoesNotConferMoralLegitimacy

criticalJuridicalDehumanisationReadingStaysAttributedAsInterpretation :
  Terra.CriticalDehumanisationReadingIsLiteralMaboHolding → ⊥
criticalJuridicalDehumanisationReadingStaysAttributedAsInterpretation =
  Terra.criticalReadingDoesNotBecomeLiteralHolding

------------------------------------------------------------------------
-- Amalek/self-sealing extension: exposing blind spot can be swallowed by chart.
------------------------------------------------------------------------

selfSealingCorrectionWitness : SelfSeal.SelfSealingCorrectionWitness SelfSeal.canonicalLoop
selfSealingCorrectionWitness = SelfSeal.canonicalSelfSealingWitness

blindSpotDisclosureMayBeReadAsConfirmation :
  SelfSeal.disclosureOfBlindSpotReadAsChartConfirmation
    SelfSeal.canonicalBlindSpotConfirmationLoop ≡ true
blindSpotDisclosureMayBeReadAsConfirmation = refl

blindSpotDisclosureDoesNotForceRevision :
  SelfSeal.disclosureCausesAutomaticRevision
    SelfSeal.canonicalBlindSpotConfirmationLoop ≡ false
blindSpotDisclosureDoesNotForceRevision = refl

terminalisationHasAdditionalCorrectionClosureRisk :
  Compression.terminalisationHasExtraCorrectionClosureRisk
    Compression.canonicalDominantChartEpistemicCompressionBoundary ≡ true
terminalisationHasAdditionalCorrectionClosureRisk = refl

closedCorrectionLoopDoesNotProveChartTrue : SelfSeal.ClosedLoopProvesUnderlyingChartTrue → ⊥
closedCorrectionLoopDoesNotProveChartTrue = SelfSeal.closedLoopDoesNotProveChartTrue

------------------------------------------------------------------------
-- Climate forum / enforcement architecture.
------------------------------------------------------------------------

pabaiAppealNotEncodedAsFinal :
  Climate.proceedingState Climate.pabaiFirstInstanceAndAppeal
  ≡ Climate.firstInstanceDecidedAppealPending
pabaiAppealNotEncodedAsFinal = refl

billyHasViolationAndPositiveRemedyReceipt :
  Climate.violationOrInvalidityFound Climate.billyTorresStraitViews ≡ true
  × Climate.positiveRemedySpecified Climate.billyTorresStraitViews ≡ true
billyHasViolationAndPositiveRemedyReceipt = refl , refl

billyTreatyViewNotAustralianDomesticWrit :
  Climate.directlySelfExecutingInAustralianDomesticCourt Climate.billyTorresStraitViews ≡ false
billyTreatyViewNotAustralianDomesticWrit = refl

neubauerHasLegislativeCorrectionPower :
  Climate.canRequireLegislativeCorrection Climate.neubauerConstitutionalDecision ≡ true
neubauerHasLegislativeCorrectionPower = refl

legalFindingDoesNotEqualEffectiveCompulsion : Climate.FindingViolationMeansDomesticCompulsion → ⊥
legalFindingDoesNotEqualEffectiveCompulsion = Climate.findingDoesNotEqualDomesticCompulsion

culturalLossLegalVisibilityIsRegimeRelative :
  Climate.culturalLossVisibility Climate.generalNegligenceRegime ≡
  Climate.culturalLossVisibility Climate.nativeTitleCompensationRegime → ⊥
culturalLossLegalVisibilityIsRegimeRelative = Climate.regimeChangesLegalVisibility

legalVisibilityDoesNotCreateUnderlyingHarm :
  Climate.legalRegimeDeterminesWhetherTheUnderlyingHarmExists
    Climate.canonicalCulturalLossRegimeBoundary ≡ false
legalVisibilityDoesNotCreateUnderlyingHarm = refl

------------------------------------------------------------------------
-- Combined diagnostic.
------------------------------------------------------------------------

systemDiagnostic : Cross.SystemIsWhatItDoesDiagnosticBoundary
systemDiagnostic = Cross.canonicalSystemIsWhatItDoesDiagnosticBoundary

declaredPurposeNotRealizedOperation :
  Cross.declaredPurposeEqualsRealizedOperation systemDiagnostic ≡ false
declaredPurposeNotRealizedOperation = refl

observerInvisibilityNotNonexistence :
  Cross.observerInvisibilityEqualsNonexistence systemDiagnostic ≡ false
observerInvisibilityNotNonexistence = refl

correctionAttemptDoesNotAlwaysOpenSystem :
  Cross.correctionAttemptAlwaysOpensSystem systemDiagnostic ≡ false
correctionAttemptDoesNotAlwaysOpenSystem = refl

legalFindingNotEffectiveCompulsion :
  Cross.legalFindingEqualsEffectiveCompulsion systemDiagnostic ≡ false
legalFindingNotEffectiveCompulsion = refl

------------------------------------------------------------------------
-- Final no-collapse laws for ITIR/SensibLaw consumers.
------------------------------------------------------------------------

data SystemClaimedPurposeOverridesObservedPractice : Set where
data NonRecognitionMeansNonexistence : Set where
data LaterLegalCorrectionMeansPriorRuleWasNeverLaw : Set where
data SuccessfulLegalMeritsAutomaticallySupplyEnforcement : Set where
data CorrectionChallengeAlwaysDisconfirmsClosedChart : Set where

claimedPurposeDoesNotOverrideObservedPractice :
  SystemClaimedPurposeOverridesObservedPractice → ⊥
claimedPurposeDoesNotOverrideObservedPractice ()

nonRecognitionDoesNotMeanNonexistence : NonRecognitionMeansNonexistence → ⊥
nonRecognitionDoesNotMeanNonexistence ()

laterCorrectionDoesNotRewritePriorLegalOperation :
  LaterLegalCorrectionMeansPriorRuleWasNeverLaw → ⊥
laterCorrectionDoesNotRewritePriorLegalOperation ()

meritsDoNotAutomaticallySupplyEnforcement :
  SuccessfulLegalMeritsAutomaticallySupplyEnforcement → ⊥
meritsDoNotAutomaticallySupplyEnforcement ()

closedChartCanAbsorbCorrectionChallenge :
  CorrectionChallengeAlwaysDisconfirmsClosedChart → ⊥
closedChartCanAbsorbCorrectionChallenge ()
