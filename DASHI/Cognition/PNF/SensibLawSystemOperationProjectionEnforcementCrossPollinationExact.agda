module DASHI.Cognition.PNF.SensibLawSystemOperationProjectionEnforcementCrossPollinationExact where

------------------------------------------------------------------------
-- SYSTEM OPERATION / VISIBILITY / CORRECTION / ENFORCEMENT CROSS-POLLINATION
--
-- This owner joins four generic theorem families without collapsing them:
--   1. what the system declares;
--   2. what the system operationally does;
--   3. what its observer can or cannot make visible;
--   4. what correction/enforcement channels can change.
--
-- The result is a reusable ITIR/SensibLaw diagnostic, not one master social or
-- legal theory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as Operation
import DASHI.Core.ObserverVisibilityExistenceNoncollapseExact as Visibility
import DASHI.Core.SelfSealingCorrectionLoopExact as SelfSeal
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek
import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusTemporalLegalOperationExact as Terra
import DASHI.Cognition.PNF.SensibLawClimateForumCompulsionEnforcementLatticeExact as Climate

------------------------------------------------------------------------
-- "A system is what it does" is operational, not mind-reading.
------------------------------------------------------------------------

posiwidBoundary : Operation.POSIWIDSourceBoundary
posiwidBoundary = Operation.canonicalPOSIWIDSourceBoundary

operationDoesNotProveIntent :
  Operation.observedOperationProvesSubjectiveIntent
    Operation.canonicalOperationalDescriptionBoundary ≡ false
operationDoesNotProveIntent = refl

missionStatementCannotDetermineEffect : Operation.MissionStatementDeterminesSystemEffect → ⊥
missionStatementCannotDetermineEffect = Operation.missionStatementDoesNotDetermineEffect

correctionResponseCountsAsOperation :
  Operation.correctionResponseIsPartOfObservableOperation
    Operation.canonicalOperationalDescriptionBoundary ≡ true
correctionResponseCountsAsOperation = refl

------------------------------------------------------------------------
-- What is invisible to an observer does not thereby cease to exist.
------------------------------------------------------------------------

visibilityBoundary : Visibility.VisibilityExistenceBoundary
visibilityBoundary = Visibility.canonicalVisibilityExistenceBoundary

invisibleDoesNotMeanNonexistent : Visibility.InvisibleMeansNonexistent → ⊥
invisibleDoesNotMeanNonexistent = Visibility.invisibleDoesNotMeanNonexistent

observerCannotRecoverExistenceFromVisibilityAlone :
  INF.FactorsThrough Visibility.demoVisibility Visibility.demoExistence → ⊥
observerCannotRecoverExistenceFromVisibilityAlone =
  Visibility.invisibleToDemoObserverDoesNotDetermineNonexistence

recognitionDoesNotConstituteExistence :
  Recognition.recognitionConstitutesAuthorityByDefault
    Recognition.canonicalRecognitionConstitutionBoundary ≡ false
recognitionDoesNotConstituteExistence = refl

------------------------------------------------------------------------
-- Mabo supplies an exact authority-bearing historical instance.
------------------------------------------------------------------------

preMaboRuleWasLegallyOperative :
  Terra.preMaboDoctrineLegallyOperative Terra.canonicalTerraNulliusTemporalBoundary ≡ true
preMaboRuleWasLegallyOperative = refl

preMaboDiscriminatoryBasisIsNotErased :
  Terra.discriminatoryBasisPartOfDoctrinalHistory Terra.canonicalTerraNulliusTemporalBoundary ≡ true
preMaboDiscriminatoryBasisIsNotErased = refl

maboChangedLandRightsConsequences :
  Terra.maboChangedCommonLawLandRightsConsequences Terra.canonicalTerraNulliusTemporalBoundary ≡ true
maboChangedLandRightsConsequences = refl

maboDidNotMakeEarlierDoctrineNeverOperate :
  Terra.LaterRejectionMeansEarlierRuleNeverOperated → ⊥
maboDidNotMakeEarlierDoctrineNeverOperate = Terra.laterRejectionDoesNotEraseHistoricalOperation

legalOperationDoesNotEqualLegitimacy : Terra.LegalValidityMeansMoralLegitimacy → ⊥
legalOperationDoesNotEqualLegitimacy = Terra.legalValidityDoesNotConferMoralLegitimacy

criticalDehumanisationReadingIsNotBackAttributedToCourt :
  Terra.CriticalDehumanisationReadingIsLiteralMaboHolding → ⊥
criticalDehumanisationReadingIsNotBackAttributedToCourt =
  Terra.criticalReadingDoesNotBecomeLiteralHolding

------------------------------------------------------------------------
-- Amalek/self-sealing lane: correction can be absorbed as confirmation.
------------------------------------------------------------------------

selfSealingWitness : SelfSeal.SelfSealingCorrectionWitness SelfSeal.canonicalLoop
selfSealingWitness = SelfSeal.canonicalSelfSealingWitness

blindSpotDisclosureCanCollapseIntoConfirmation :
  SelfSeal.correctiveDisclosureCanBeCollapsedIntoConfirmation
    SelfSeal.canonicalCorrectionChannelBoundary ≡ true
blindSpotDisclosureCanCollapseIntoConfirmation = refl

amalekClosedLoopHasNoIndependentCorrection :
  Amalek.correctionChannelIndependent Amalek.canonicalClosedAuthorityRisk ≡ false
amalekClosedLoopHasNoIndependentCorrection = refl

terminalisationHasExtraCorrectionClosureRisk :
  Compression.terminalisationHasExtraCorrectionClosureRisk
    Compression.canonicalDominantChartEpistemicCompressionBoundary ≡ true
terminalisationHasExtraCorrectionClosureRisk = refl

closedLoopDoesNotProveChartTrue : SelfSeal.ClosedLoopProvesUnderlyingChartTrue → ⊥
closedLoopDoesNotProveChartTrue = SelfSeal.closedLoopDoesNotProveChartTrue

------------------------------------------------------------------------
-- Climate-forum lane: a finding is not an enforcement channel.
------------------------------------------------------------------------

pabaiAppealIsStillPendingInReceipt :
  Climate.proceedingState Climate.pabaiFirstInstanceAndAppeal
  ≡ Climate.firstInstanceDecidedAppealPending
pabaiAppealIsStillPendingInReceipt = refl

billyViolationAndPositiveRemedyCoexist :
  Climate.violationOrInvalidityFound Climate.billyTorresStraitViews ≡ true
  × Climate.positiveRemedySpecified Climate.billyTorresStraitViews ≡ true
billyViolationAndPositiveRemedyCoexist = refl , refl

billyRemedyIsNotDirectAustralianDomesticWrit :
  Climate.directlySelfExecutingInAustralianDomesticCourt Climate.billyTorresStraitViews ≡ false
billyRemedyIsNotDirectAustralianDomesticWrit = refl

neubauerHadLegislativeCorrectionChannel :
  Climate.canRequireLegislativeCorrection Climate.neubauerConstitutionalDecision ≡ true
neubauerHadLegislativeCorrectionChannel = refl

findingDoesNotCollapseToCompulsion : Climate.FindingViolationMeansDomesticCompulsion → ⊥
findingDoesNotCollapseToCompulsion = Climate.findingDoesNotEqualDomesticCompulsion

------------------------------------------------------------------------
-- Unified diagnostic surface.
------------------------------------------------------------------------

data DiagnosticQuestion : Set where
  whatDoesSystemDeclare : DiagnosticQuestion
  whatDoesSystemDo : DiagnosticQuestion
  whatCanSystemSee : DiagnosticQuestion
  whatDoesSystemTreatAsNonexistent : DiagnosticQuestion
  howDoesSystemHandleCorrection : DiagnosticQuestion
  whatAuthorityAttachesToItsOutput : DiagnosticQuestion
  whatEnforcementChannelExists : DiagnosticQuestion
  whatMaterialStatePersists : DiagnosticQuestion


record SystemIsWhatItDoesDiagnosticBoundary : Set where
  constructor system-is-what-it-does-diagnostic-boundary
  field
    declaredPurposeEqualsRealizedOperation : Bool
    declaredPurposeEqualsRealizedOperationIsFalse :
      declaredPurposeEqualsRealizedOperation ≡ false
    observerInvisibilityEqualsNonexistence : Bool
    observerInvisibilityEqualsNonexistenceIsFalse :
      observerInvisibilityEqualsNonexistence ≡ false
    legalRecognitionEqualsConstitutionOfUnderlyingRelation : Bool
    legalRecognitionEqualsConstitutionOfUnderlyingRelationIsFalse :
      legalRecognitionEqualsConstitutionOfUnderlyingRelation ≡ false
    correctionAttemptAlwaysOpensSystem : Bool
    correctionAttemptAlwaysOpensSystemIsFalse :
      correctionAttemptAlwaysOpensSystem ≡ false
    legalFindingEqualsEffectiveCompulsion : Bool
    legalFindingEqualsEffectiveCompulsionIsFalse :
      legalFindingEqualsEffectiveCompulsion ≡ false
    historicalLegalValidityEqualsLegitimacy : Bool
    historicalLegalValidityEqualsLegitimacyIsFalse :
      historicalLegalValidityEqualsLegitimacy ≡ false
    realizedOperationMayBeAuditedWithoutInferringIntent : Bool
    realizedOperationMayBeAuditedWithoutInferringIntentIsTrue :
      realizedOperationMayBeAuditedWithoutInferringIntent ≡ true

open SystemIsWhatItDoesDiagnosticBoundary public

canonicalSystemIsWhatItDoesDiagnosticBoundary :
  SystemIsWhatItDoesDiagnosticBoundary
canonicalSystemIsWhatItDoesDiagnosticBoundary =
  system-is-what-it-does-diagnostic-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- No master-theory promotion.
------------------------------------------------------------------------

data POSIWIDEqualsAmalek : Set where
data MaboEqualsClimateLitigation : Set where
data VisibilityFailureAlwaysMeansPoliticalOppression : Set where
data EnforcementWeaknessProvesMeritsWrong : Set where

posiwidDoesNotEqualAmalek : POSIWIDEqualsAmalek → ⊥
posiwidDoesNotEqualAmalek ()

maboDoesNotEqualClimateLitigation : MaboEqualsClimateLitigation → ⊥
maboDoesNotEqualClimateLitigation ()

visibilityFailureDoesNotAutomaticallyProveOppression :
  VisibilityFailureAlwaysMeansPoliticalOppression → ⊥
visibilityFailureDoesNotAutomaticallyProveOppression ()

enforcementWeaknessDoesNotNegateMerits : EnforcementWeaknessProvesMeritsWrong → ⊥
enforcementWeaknessDoesNotNegateMerits ()
