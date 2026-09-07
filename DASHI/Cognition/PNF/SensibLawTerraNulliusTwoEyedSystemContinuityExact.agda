module DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact where

------------------------------------------------------------------------
-- TERRA NULLIUS -> TWO-EYED / REALISED-REMEDY STRUCTURAL CONTINUITY
--
-- This owner asks a narrower operational question than doctrinal validity:
-- after the foundational doctrine is rejected, has the relation by which one
-- order defines, observes and corrects the other actually changed?
--
-- Source-attribution boundary:
--   * Mabo/Brennan propositions remain source-owned upstream;
--   * Billy/HRC remedy propositions remain Committee-owned upstream;
--   * Two-Eyed Seeing / Kimmerer/Indigenous-knowledge material remains
--     source-bounded upstream;
--   * the continuity criterion below is a SensibLaw/DASHI construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusJuridicalHumanityOperationalEquivalenceExact as Humanity
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Remedy
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.AmalekAuthorityProjectionBoundary as Amalek

------------------------------------------------------------------------
-- Foundational relation is already classified strongly.
------------------------------------------------------------------------

terraNulliusWasJuridicallyNonHumanAtFoundationalRelation :
  Humanity.classify Humanity.terraNulliusCriterion
  ≡ Humanity.juridicallyNonHumanNonconstitutive
terraNulliusWasJuridicallyNonHumanAtFoundationalRelation = refl

terraNulliusDeniedConstitutiveHumanity :
  Humanity.legallyConstitutiveHumanityDenied
    Humanity.terraNulliusJuridicalNonHumanityReading ≡ true
terraNulliusDeniedConstitutiveHumanity = refl

------------------------------------------------------------------------
-- Operational repair coordinates.
------------------------------------------------------------------------

data RelationTransformationCoordinate : Set where
  doctrineRejected
  indigenousOrderConstitutiveStanding
  communityAuthorityBearing
  landCountryControl
  communityDefinedOutcomeAuthority
  independentCorrectionAvailable
  externalEvidenceCanChangeDecision
  dissentRemainsAdmissibleEvidence
  compensationAndReparationRealised
  recurrencePreventionRealised
  : RelationTransformationCoordinate

data CoordinateState : Set where
  paid
  partial
  open
  sourceOutcomeRequired
  : CoordinateState

currentCoordinateState : RelationTransformationCoordinate → CoordinateState
currentCoordinateState doctrineRejected = paid
currentCoordinateState indigenousOrderConstitutiveStanding = partial
currentCoordinateState communityAuthorityBearing = open
currentCoordinateState landCountryControl = open
currentCoordinateState communityDefinedOutcomeAuthority = open
currentCoordinateState independentCorrectionAvailable = open
currentCoordinateState externalEvidenceCanChangeDecision = open
currentCoordinateState dissentRemainsAdmissibleEvidence = open
currentCoordinateState compensationAndReparationRealised = open
currentCoordinateState recurrencePreventionRealised = sourceOutcomeRequired

doctrineIsRejected : currentCoordinateState doctrineRejected ≡ paid
doctrineIsRejected = refl

landControlStillOpen : currentCoordinateState landCountryControl ≡ open
landControlStillOpen = refl

communityAuthorityStillOpen : currentCoordinateState communityAuthorityBearing ≡ open
communityAuthorityStillOpen = refl

compensationStillOpen : currentCoordinateState compensationAndReparationRealised ≡ open
compensationStillOpen = refl

------------------------------------------------------------------------
-- Structural continuity is not historical identity.  It asks whether the same
-- relation-defining asymmetry survives after labels/doctrine change.
------------------------------------------------------------------------

data StructuralContinuityClassification : Set where
  foundationalRelationTransformed
  structuralContinuityRisk
  insufficientEvidence
  : StructuralContinuityClassification

record RelationTransformationEvidence : Set where
  constructor relation-transformation-evidence
  field
    oldDoctrineRejected : Bool
    indigenousAuthorityConstitutiveInRealizedProcess : Bool
    communityOutcomeCanOverrideStateSelfAssessment : Bool
    independentCorrectionActuallyAvailable : Bool
    landCountryControlMateriallyChanged : Bool
    compensationReparationRealised : Bool
    recurrencePreventionObserved : Bool

open RelationTransformationEvidence public

classifyTransformation : RelationTransformationEvidence → StructuralContinuityClassification
classifyTransformation (relation-transformation-evidence true true true true true true true) =
  foundationalRelationTransformed
classifyTransformation (relation-transformation-evidence true false false false false false false) =
  structuralContinuityRisk
classifyTransformation _ = insufficientEvidence

------------------------------------------------------------------------
-- Synthetic theorem fixture: doctrinal rejection alone can coexist with an
-- operationally untransformed relation.
------------------------------------------------------------------------

doctrinalRejectionOnlyFixture : RelationTransformationEvidence
doctrinalRejectionOnlyFixture = relation-transformation-evidence
  true false false false false false false

doctrinalRejectionOnlyStillLeavesStructuralRisk :
  classifyTransformation doctrinalRejectionOnlyFixture ≡ structuralContinuityRisk
doctrinalRejectionOnlyStillLeavesStructuralRisk = refl

fullyTransformedFixture : RelationTransformationEvidence
fullyTransformedFixture = relation-transformation-evidence
  true true true true true true true

fullyTransformedFixtureClosesRelation :
  classifyTransformation fullyTransformedFixture ≡ foundationalRelationTransformed
fullyTransformedFixtureClosesRelation = refl

------------------------------------------------------------------------
-- Same declaration, different correction/authority state: declaration is not
-- a sufficient statistic for decolonial relation transformation.
------------------------------------------------------------------------

data RemedyRelationState : Set where
  stateDeclaredRepairWithoutAuthorityShift
  stateDeclaredRepairWithAuthorityShift
  : RemedyRelationState

data DeclaredRepairSurface : Set where
  sameDeclaredRepair : DeclaredRepairSurface

data RealizedAuthorityRelation : Set where
  stateMediatedAuthorityRelation
  communityAuthorityBearingRelation
  : RealizedAuthorityRelation

declaredRepairSurface : RemedyRelationState → DeclaredRepairSurface
declaredRepairSurface _ = sameDeclaredRepair

realizedAuthorityRelation : RemedyRelationState → RealizedAuthorityRelation
realizedAuthorityRelation stateDeclaredRepairWithoutAuthorityShift = stateMediatedAuthorityRelation
realizedAuthorityRelation stateDeclaredRepairWithAuthorityShift = communityAuthorityBearingRelation

authorityRelationsDiffer :
  realizedAuthorityRelation stateDeclaredRepairWithoutAuthorityShift
  ≡ realizedAuthorityRelation stateDeclaredRepairWithAuthorityShift → ⊥
authorityRelationsDiffer ()

declaredRepairCannotRecoverAuthorityTransformation :
  INF.FactorsThrough declaredRepairSurface realizedAuthorityRelation → ⊥
declaredRepairCannotRecoverAuthorityTransformation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      stateDeclaredRepairWithoutAuthorityShift
      stateDeclaredRepairWithAuthorityShift
      refl
      authorityRelationsDiffer)

------------------------------------------------------------------------
-- Two-Eyed Seeing: state and community strands remain co-present, not fused.
------------------------------------------------------------------------

sharedObservationDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistory = refl

extractedClaimDoesNotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedClaimDoesNotRecoverCommunityAuthority = IK.propositionCannotRecoverAuthority

stateObservationDoesNotExhaustCommunityOutcome :
  Country.stateObservationExhaustsCommunityOutcome
    Country.canonicalBraidedRemedyAssessment ≡ false
stateObservationDoesNotExhaustCommunityOutcome = refl

communityOutcomeCanReopenImplementation :
  Country.communityOutcomeCanReopenImplementation
    Country.canonicalBraidedRemedyAssessment ≡ true
communityOutcomeCanReopenImplementation = refl

administrativeConsultationDoesNotRecoverCommunityDefinedOutcome :
  INF.FactorsThrough
    Remedy.administrativeConsultationObserver
    Remedy.communityConsultationOutcome → ⊥
administrativeConsultationDoesNotRecoverCommunityDefinedOutcome =
  Remedy.administrativeConsultationCannotRecoverCommunityOutcome

------------------------------------------------------------------------
-- POSIWID: correction handling is itself part of what the system does.
------------------------------------------------------------------------

operationalBoundary : POSIWID.OperationalDescriptionBoundary
operationalBoundary = POSIWID.canonicalOperationalDescriptionBoundary

correctionResponseIsObservableOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation operationalBoundary ≡ true
correctionResponseIsObservableOperation = refl

declarationCannotOverrideRepeatedRealizedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect operationalBoundary ≡ false
declarationCannotOverrideRepeatedRealizedEffect = refl

operationDoesNotByItselfProvePrivateIntent :
  POSIWID.observedOperationProvesSubjectiveIntent operationalBoundary ≡ false
operationDoesNotByItselfProvePrivateIntent = refl

------------------------------------------------------------------------
-- Amalek is the stronger correction-closure frontier.  We do NOT claim all of
-- these coordinates for terra nullius or current Australian remedy practice by
-- default; the abstract closed-loop owner tells us what extra evidence would be
-- required to make that stronger classification.
------------------------------------------------------------------------

data CorrectionClosureCoordinate : Set where
  authoritySelfValidates
  externalCorrectionDelegitimised
  doubtPenalised
  dissentReclassifiedAsFault
  independentCorrectionClosed
  : CorrectionClosureCoordinate

data CorrectionClosureEvidence : Set where
  notYetPaid
  separatelySourcePaid
  : CorrectionClosureEvidence

currentTerraNulliusClosureEvidence : CorrectionClosureCoordinate → CorrectionClosureEvidence
currentTerraNulliusClosureEvidence _ = notYetPaid

amalekClosedAuthorityRisk : Amalek.ClosedAuthorityLoop
amalekClosedAuthorityRisk = Amalek.canonicalClosedAuthorityRisk

amalekCanonicalLoopHasNoIndependentCorrection :
  Amalek.correctionChannelIndependent amalekClosedAuthorityRisk ≡ false
amalekCanonicalLoopHasNoIndependentCorrection = refl

record SystemFunctionBoundary : Set where
  constructor system-function-boundary
  field
    doctrinalRejectionAloneTransformsFoundationalRelation : Bool
    doctrinalRejectionAloneTransformsFoundationalRelationIsFalse :
      doctrinalRejectionAloneTransformsFoundationalRelation ≡ false
    stateSelfReportAloneClosesCommunityDefinedJustice : Bool
    stateSelfReportAloneClosesCommunityDefinedJusticeIsFalse :
      stateSelfReportAloneClosesCommunityDefinedJustice ≡ false
    affectedCommunityOutcomeMustRemainIndependentStrand : Bool
    affectedCommunityOutcomeMustRemainIndependentStrandIsTrue :
      affectedCommunityOutcomeMustRemainIndependentStrand ≡ true
    landCountryControlIsMaterialCoordinate : Bool
    landCountryControlIsMaterialCoordinateIsTrue : landCountryControlIsMaterialCoordinate ≡ true
    correctionCanBePartOfOperationalClassification : Bool
    correctionCanBePartOfOperationalClassificationIsTrue :
      correctionCanBePartOfOperationalClassification ≡ true
    repeatedRealizedAuthorityErasureMaySupportContinuityClassification : Bool
    repeatedRealizedAuthorityErasureMaySupportContinuityClassificationIsTrue :
      repeatedRealizedAuthorityErasureMaySupportContinuityClassification ≡ true
    operationalContinuityClassificationProvesPrivateRacistIntent : Bool
    operationalContinuityClassificationProvesPrivateRacistIntentIsFalse :
      operationalContinuityClassificationProvesPrivateRacistIntent ≡ false

open SystemFunctionBoundary public

canonicalSystemFunctionBoundary : SystemFunctionBoundary
canonicalSystemFunctionBoundary = system-function-boundary
  false refl
  false refl
  true refl
  true refl
  true refl
  true refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data MaboRejectedTerraNulliusThereforeColonialRelationFullyTransformed : Set where
data StateConsultedThereforeCommunityAuthorityBearing : Set where
data CommunityOutcomeEqualsStateImplementationReport : Set where
data StructuralContinuityRiskMeansLiteralHistoricalDoctrineIdentity : Set where
data StructuralContinuityRiskProvesPrivateIntent : Set where

maboRejectionDoesNotByItselfCloseRelation :
  MaboRejectedTerraNulliusThereforeColonialRelationFullyTransformed → ⊥
maboRejectionDoesNotByItselfCloseRelation ()

consultationDoesNotByItselfPayCommunityAuthority :
  StateConsultedThereforeCommunityAuthorityBearing → ⊥
consultationDoesNotByItselfPayCommunityAuthority ()

communityOutcomeDoesNotCollapseToStateReport :
  CommunityOutcomeEqualsStateImplementationReport → ⊥
communityOutcomeDoesNotCollapseToStateReport ()

structuralContinuityDoesNotMeanLiteralDoctrineIdentity :
  StructuralContinuityRiskMeansLiteralHistoricalDoctrineIdentity → ⊥
structuralContinuityDoesNotMeanLiteralDoctrineIdentity ()

structuralContinuityDoesNotProvePrivateIntent :
  StructuralContinuityRiskProvesPrivateIntent → ⊥
structuralContinuityDoesNotProvePrivateIntent ()
