module DASHI.Cognition.PNF.SensibLawCountryGenocideWrongTypeEnforcementEverything where

------------------------------------------------------------------------
-- COUNTRY / GENOCIDE / WRONGTYPE / ENFORCEMENT CAPSTONE
--
-- Classification and enforcement are separate BIDI problems:
--
--   evidence -> Convention WrongType elements -> classification status
--
-- and
--
--   desired outcome -> legal mechanism -> jurisdiction/procedure/actor receipt.
--
-- A narrow Convention mismatch does not erase other wrongs.  A binding legal
-- determination does not itself supply a coercive execution actuator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawCountryRelationalLossGenocideBoundaryExact as Genocide
import DASHI.Cognition.PNF.SensibLawGenocideConventionWrongTypeBidiExact as Wrong
import DASHI.Cognition.PNF.SensibLawGenocideEnforcementMeansBidiExact as Enforce
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as GenericWrongBidi
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as ElementAlgebra
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- Convention classification remains narrow and elemented.
------------------------------------------------------------------------

conventionWrongType : Ontology.WrongType
conventionWrongType = Wrong.genocideConventionWrongType

specificIntentUsesMentalStateElement :
  Wrong.axisLegalElementKind Wrong.specificIntentAxis
  ≡ ElementAlgebra.mentalStateElement
specificIntentUsesMentalStateElement = refl

record CountryRelationalConventionProbe : Set where
  constructor country-relational-convention-probe
  field
    relationLossSource : Genocide.RelationalDestructionReceipt
    conventionElementState : Wrong.ConventionElementState
    conventionStatus : Wrong.ConventionWrongTypeStatus
    statusMatchesClassifier :
      conventionStatus ≡ Wrong.classifyConventionWrongType conventionElementState
    relationalLossStillIndependentlyRepresented : Bool
    relationalLossStillIndependentlyRepresentedIsTrue :
      relationalLossStillIndependentlyRepresented ≡ true

open CountryRelationalConventionProbe public

------------------------------------------------------------------------
-- Synthetic classification probe: protected-group premise is supplied, while
-- enumerated-act and specific-intent producers remain open.  This is NOT a
-- classification of Griffiths or another named event as genocide.
------------------------------------------------------------------------

relationalLossConventionProbe : CountryRelationalConventionProbe
relationalLossConventionProbe = country-relational-convention-probe
  Genocide.griffithsRelationalLossReceipt
  (Wrong.convention-element-state
    Wrong.elementSatisfied
    Wrong.elementOpen
    Wrong.elementOpen
    "synthetic Convention probe over a source-accepted relational-loss receipt; no named-event genocide classification"
    "SensibLawCountryGenocideWrongTypeEnforcementEverything")
  Wrong.conventionWrongTypeOpen
  refl
  true refl

------------------------------------------------------------------------
-- Bringing Them Home source-specific institutional finding can close the three
-- Convention axes in that source lane without becoming a criminal conviction.
------------------------------------------------------------------------

bringingThemHomeConventionProbe : Wrong.ConventionElementState
bringingThemHomeConventionProbe = Wrong.convention-element-state
  Wrong.elementSatisfied
  Wrong.elementSatisfied
  Wrong.elementSatisfied
  "Bringing Them Home institutional inquiry finding as already represented in SensibLawCountryRelationalLossGenocideBoundaryExact"
  "source-specific institutional finding; not criminal conviction"

bringingThemHomeClassifierClosesOnSourceFinding :
  Wrong.classifyConventionWrongType bringingThemHomeConventionProbe
  ≡ Wrong.conventionWrongTypeClosed
bringingThemHomeClassifierClosesOnSourceFinding = refl

bringingThemHomeStillNotCriminalConviction :
  Genocide.thisReceiptIsJudicialCriminalConviction
    Genocide.bringingThemHomeGenocideFinding ≡ false
bringingThemHomeStillNotCriminalConviction = refl

------------------------------------------------------------------------
-- WrongType BIDI: element closure is upstream of applicability/violation/etc.
------------------------------------------------------------------------

wrongTypeClassificationDoesNotSkipApplicability :
  GenericWrongBidi.WrongTypeInterpretationAutomaticallyApplicable → ⊥
wrongTypeClassificationDoesNotSkipApplicability =
  GenericWrongBidi.wrongTypeInterpretationDoesNotAutoApply

applicabilityDoesNotSkipViolation :
  GenericWrongBidi.ApplicableAutomaticallyViolated → ⊥
applicabilityDoesNotSkipViolation = GenericWrongBidi.applicabilityDoesNotAutoViolate

violationDoesNotSkipLiability :
  GenericWrongBidi.ViolationAutomaticallyLiable → ⊥
violationDoesNotSkipLiability = GenericWrongBidi.violationDoesNotAutoCreateLiability

liabilityDoesNotAutoSelectRemedy :
  GenericWrongBidi.LiabilityAutomaticallySelectsRemedy → ⊥
liabilityDoesNotAutoSelectRemedy = GenericWrongBidi.liabilityDoesNotAutoSelectRemedy

------------------------------------------------------------------------
-- Reverse reclassification: failing the genocide mental-state element does not
-- collapse the event to 'no wrong'.
------------------------------------------------------------------------

intentFailureRoutesToHumanRightsInquiry : Wrong.WrongTypeReverseRoute
intentFailureRoutesToHumanRightsInquiry = Wrong.intentFailureToHumanRightsRoute

relationalLossRoutesToIndependentHarmInquiry : Wrong.WrongTypeReverseRoute
relationalLossRoutesToIndependentHarmInquiry = Wrong.culturalLossToRelationalRoute

conventionFailureDoesNotMeanNoWrong :
  Wrong.ConventionGenocideFailureMeansNoWrongOccurred → ⊥
conventionFailureDoesNotMeanNoWrong = Wrong.conventionFailureDoesNotMeanNoWrong

------------------------------------------------------------------------
-- Enforcement BIDI: classify the desired outcome before selecting the forum.
------------------------------------------------------------------------

stopOngoingConductRoute : Enforce.EnforcementRoute
stopOngoingConductRoute = Enforce.stopConductRoute

punishIndividualRoute : Enforce.EnforcementRoute
punishIndividualRoute = Enforce.punishIndividualRoute

stateResponsibilityRoute : Enforce.EnforcementRoute
stateResponsibilityRoute = Enforce.stateResponsibilityRoute

enforceFinalJudgmentRoute : Enforce.EnforcementRoute
enforceFinalJudgmentRoute = Enforce.enforceJudgmentRoute

stoppingConductFirstNeedsInterstateProvisionalMeasurePredicate :
  Enforce.firstRequiredPrerequisite stopOngoingConductRoute
  ≡ Enforce.provisionalMeasuresJurisdictionAndPlausibilityReceipt
stoppingConductFirstNeedsInterstateProvisionalMeasurePredicate = refl

individualPunishmentFirstNeedsCriminalJurisdiction :
  Enforce.firstRequiredPrerequisite punishIndividualRoute
  ≡ Enforce.competentDomesticTribunalJurisdictionReceipt
individualPunishmentFirstNeedsCriminalJurisdiction = refl

stateResponsibilityFirstNeedsInterstateJurisdiction :
  Enforce.firstRequiredPrerequisite stateResponsibilityRoute
  ≡ Enforce.interstateDisputeJurisdictionReceipt
stateResponsibilityFirstNeedsInterstateJurisdiction = refl

judgmentEnforcementStartsFromNonComplianceReceipt :
  Enforce.firstRequiredPrerequisite enforceFinalJudgmentRoute
  ≡ Enforce.nonComplianceReceipt
judgmentEnforcementStartsFromNonComplianceReceipt = refl

------------------------------------------------------------------------
-- "No teeth" becomes a fibre, not a slogan.
------------------------------------------------------------------------

icjNormativeObligationPresent :
  Enforce.icjTeethState Enforce.normativeObligation ≡ Enforce.present
icjNormativeObligationPresent = refl

icjAdjudicativeAuthorityConditional :
  Enforce.icjTeethState Enforce.adjudicativeAuthority ≡ Enforce.conditional
icjAdjudicativeAuthorityConditional = refl

icjOwnCoerciveExecutionArmAbsent :
  Enforce.icjTeethState Enforce.coerciveExecutionArm ≡ Enforce.absentAtForum
icjOwnCoerciveExecutionArmAbsent = refl

icjPoliticalEnforcementExternallyDependent :
  Enforce.icjTeethState Enforce.politicalEnforcementActuator
  ≡ Enforce.externallyDependent
icjPoliticalEnforcementExternallyDependent = refl

securityCouncilActionIsNotAutomatic :
  Enforce.securityCouncilActionAutomatic Enforce.canonicalNoTeethDecomposition ≡ false
securityCouncilActionIsNotAutomatic = refl

substantiveCouncilActionCanBeVetoBlocked :
  Enforce.substantiveCouncilActionCanBeVetoBlocked
    Enforce.canonicalNoTeethDecomposition ≡ true
substantiveCouncilActionCanBeVetoBlocked = refl

------------------------------------------------------------------------
-- Enforcement-power mismatch is itself a WrongType/remedy planning residual.
------------------------------------------------------------------------

data EnforcementResidual : Set where
  noJurisdictionYet : EnforcementResidual
  bindingOrderWithoutOwnExecutionArm : EnforcementResidual
  nonComplianceAwaitingExternalActuator : EnforcementResidual
  punitiveForumNotYetAvailable : EnforcementResidual
  domesticImplementationMissing : EnforcementResidual


data EnforcementProducer : Set where
  produceJurisdictionReceipt : EnforcementProducer
  produceDomesticImplementationReceipt : EnforcementProducer
  produceSecurityCouncilDecisionOrAlternativePressure : EnforcementProducer
  produceCriminalForumJurisdiction : EnforcementProducer
  produceComplianceEvidence : EnforcementProducer


producerForResidual : EnforcementResidual → EnforcementProducer
producerForResidual noJurisdictionYet = produceJurisdictionReceipt
producerForResidual bindingOrderWithoutOwnExecutionArm = produceComplianceEvidence
producerForResidual nonComplianceAwaitingExternalActuator = produceSecurityCouncilDecisionOrAlternativePressure
producerForResidual punitiveForumNotYetAvailable = produceCriminalForumJurisdiction
producerForResidual domesticImplementationMissing = produceDomesticImplementationReceipt

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data ConventionElementsClosedMeansRemedyRealised : Set where
data BindingICJOrderMeansMaterialProtectionRealised : Set where
data SecurityCouncilRouteMeansPoliticsNoLongerMatters : Set where
data WrongTypeFailureErasesRelationalHarm : Set where

classificationDoesNotRealiseRemedy : ConventionElementsClosedMeansRemedyRealised → ⊥
classificationDoesNotRealiseRemedy ()

bindingOrderDoesNotEqualMaterialProtection : BindingICJOrderMeansMaterialProtectionRealised → ⊥
bindingOrderDoesNotEqualMaterialProtection ()

securityCouncilRouteDoesNotErasePolitics : SecurityCouncilRouteMeansPoliticsNoLongerMatters → ⊥
securityCouncilRouteDoesNotErasePolitics ()

wrongTypeMismatchDoesNotEraseRelationalHarm : WrongTypeFailureErasesRelationalHarm → ⊥
wrongTypeMismatchDoesNotEraseRelationalHarm ()
