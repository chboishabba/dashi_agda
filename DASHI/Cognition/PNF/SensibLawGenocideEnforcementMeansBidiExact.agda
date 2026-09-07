module DASHI.Cognition.PNF.SensibLawGenocideEnforcementMeansBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.PNF.SensibLawGenocideConventionEnforcementSourceAtlasExact as Sources

------------------------------------------------------------------------
-- GENOCIDE CONVENTION ENFORCEMENT MEANS BIDI
--
-- "The UN/ICJ has no teeth" is decomposed into typed enforcement topology.
-- Legal obligation, adjudication, domestic implementation, criminal punishment,
-- coercive execution and political leverage are separate coordinates.
------------------------------------------------------------------------

data EnforcementGoal : Set where
  preventFutureGenocide
  stopOngoingConduct
  punishIndividualPerpetrator
  establishStateResponsibility
  obtainStateReparation
  enforceICJJudgmentAfterNonCompliance
  monitorOrEscalateNonCompliance
  : EnforcementGoal

data MechanismKind : Set where
  domesticImplementingLegislation
  domesticCriminalTribunal
  internationalPenalTribunal
  competentUNOrganRequest
  icjInterstateMeritsRoute
  icjProvisionalMeasuresRoute
  securityCouncilArticle94Route
  domesticExecutiveOrLegislativeCompliance
  diplomaticPoliticalFollowup
  : MechanismKind

data LegalForceKind : Set where
  bindingTreatyObligation
  bindingJudicialDecision
  bindingProvisionalMeasure
  criminalPunishmentIfJurisdictionEstablished
  politicalOrInstitutionalLeverage
  domesticImplementationDependent
  : LegalForceKind

data ExecutionTopology : Set where
  selfExecutingCoerciveActuatorAbsent
  domesticStateActuatorRequired
  securityCouncilActuatorAvailableButPolitical
  tribunalPunitiveActuatorIfJurisdiction
  monitoringLeverageOnly
  : ExecutionTopology

record EnforcementMechanismReceipt : Set where
  constructor enforcement-mechanism-receipt
  field
    mechanism : MechanismKind
    sourceReference : String
    sourceAuthorityKind : String
    legalForce : LegalForceKind
    executionTopology : ExecutionTopology
    directPhysicalCoerciveArmOwnedByForum : Bool
    directPhysicalCoerciveArmOwnedByForumIsFalse :
      directPhysicalCoerciveArmOwnedByForum ≡ false
    mechanismAloneGuaranteesCompliance : Bool
    mechanismAloneGuaranteesComplianceIsFalse :
      mechanismAloneGuaranteesCompliance ≡ false

open EnforcementMechanismReceipt public

domesticLegislationReceipt : EnforcementMechanismReceipt
domesticLegislationReceipt = enforcement-mechanism-receipt
  domesticImplementingLegislation
  "Genocide Convention Article V"
  "multilateral treaty obligation"
  bindingTreatyObligation
  domesticStateActuatorRequired
  false refl
  false refl

domesticTrialReceipt : EnforcementMechanismReceipt
domesticTrialReceipt = enforcement-mechanism-receipt
  domesticCriminalTribunal
  "Genocide Convention Article VI"
  "multilateral treaty tribunal route"
  criminalPunishmentIfJurisdictionEstablished
  tribunalPunitiveActuatorIfJurisdiction
  false refl
  false refl

internationalPenalTribunalReceipt : EnforcementMechanismReceipt
internationalPenalTribunalReceipt = enforcement-mechanism-receipt
  internationalPenalTribunal
  "Genocide Convention Article VI"
  "multilateral treaty tribunal route; actual penal tribunal jurisdiction requires separate receipt"
  criminalPunishmentIfJurisdictionEstablished
  tribunalPunitiveActuatorIfJurisdiction
  false refl
  false refl

unOrganArticleVIIIReceipt : EnforcementMechanismReceipt
unOrganArticleVIIIReceipt = enforcement-mechanism-receipt
  competentUNOrganRequest
  "Genocide Convention Article VIII"
  "multilateral treaty political/institutional route"
  politicalOrInstitutionalLeverage
  monitoringLeverageOnly
  false refl
  false refl

icjMeritsReceipt : EnforcementMechanismReceipt
icjMeritsReceipt = enforcement-mechanism-receipt
  icjInterstateMeritsRoute
  "Genocide Convention Article IX + UN Charter Article 94(1)"
  "interstate treaty dispute adjudication / binding ICJ judgment for parties"
  bindingJudicialDecision
  selfExecutingCoerciveActuatorAbsent
  false refl
  false refl

icjProvisionalMeasuresReceipt : EnforcementMechanismReceipt
icjProvisionalMeasuresReceipt = enforcement-mechanism-receipt
  icjProvisionalMeasuresRoute
  "ICJ Statute Article 41 as interpreted in LaGrand (2001)"
  "ICJ binding provisional-measures jurisprudence"
  bindingProvisionalMeasure
  selfExecutingCoerciveActuatorAbsent
  false refl
  false refl

securityCouncilArticle94Receipt : EnforcementMechanismReceipt
securityCouncilArticle94Receipt = enforcement-mechanism-receipt
  securityCouncilArticle94Route
  "UN Charter Article 94(2), read with Article 27 voting"
  "UN Charter enforcement recourse after non-performance of ICJ judgment"
  politicalOrInstitutionalLeverage
  securityCouncilActuatorAvailableButPolitical
  false refl
  false refl

------------------------------------------------------------------------
-- Reverse/BIDI planner: desired outcome -> mechanism -> missing prerequisite.
------------------------------------------------------------------------

data EnforcementPrerequisite : Set where
  statePartyTreatyObligationReceipt
  domesticImplementingLawReceipt
  competentDomesticTribunalJurisdictionReceipt
  internationalPenalTribunalJurisdictionReceipt
  interstateDisputeJurisdictionReceipt
  provisionalMeasuresJurisdictionAndPlausibilityReceipt
  finalICJJudgmentReceipt
  nonComplianceReceipt
  securityCouncilDecisionReceipt
  domesticExecutiveImplementationReceipt
  : EnforcementPrerequisite

record EnforcementRoute : Set where
  constructor enforcement-route
  field
    goal : EnforcementGoal
    mechanism : EnforcementMechanismReceipt
    firstRequiredPrerequisite : EnforcementPrerequisite
    routeReference : String
    routeGuaranteesOutcome : Bool
    routeGuaranteesOutcomeIsFalse : routeGuaranteesOutcome ≡ false

open EnforcementRoute public

preventRoute : EnforcementRoute
preventRoute = enforcement-route
  preventFutureGenocide
  domesticLegislationReceipt
  domesticImplementingLawReceipt
  "Article V prevention/punishment implementation begins with domestic legislation and institutions"
  false refl

stopConductRoute : EnforcementRoute
stopConductRoute = enforcement-route
  stopOngoingConduct
  icjProvisionalMeasuresReceipt
  provisionalMeasuresJurisdictionAndPlausibilityReceipt
  "interstate route can seek binding provisional measures, but jurisdiction and case-specific predicates remain separate"
  false refl

punishIndividualRoute : EnforcementRoute
punishIndividualRoute = enforcement-route
  punishIndividualPerpetrator
  domesticTrialReceipt
  competentDomesticTribunalJurisdictionReceipt
  "individual punishment belongs to competent criminal tribunals, not to the ICJ"
  false refl

stateResponsibilityRoute : EnforcementRoute
stateResponsibilityRoute = enforcement-route
  establishStateResponsibility
  icjMeritsReceipt
  interstateDisputeJurisdictionReceipt
  "Article IX permits interstate Convention disputes, including State responsibility questions, subject to jurisdiction"
  false refl

reparationRoute : EnforcementRoute
reparationRoute = enforcement-route
  obtainStateReparation
  icjMeritsReceipt
  interstateDisputeJurisdictionReceipt
  "state reparation requires a state-responsibility/remedy route; Convention classification alone is not an execution mechanism"
  false refl

enforceJudgmentRoute : EnforcementRoute
enforceJudgmentRoute = enforcement-route
  enforceICJJudgmentAfterNonCompliance
  securityCouncilArticle94Receipt
  nonComplianceReceipt
  "Article 94(2) recourse begins only after a judgment obligation and non-performance; Council action is not automatic"
  false refl

monitorEscalateRoute : EnforcementRoute
monitorEscalateRoute = enforcement-route
  monitorOrEscalateNonCompliance
  unOrganArticleVIIIReceipt
  statePartyTreatyObligationReceipt
  "Article VIII permits a Contracting Party to call on competent UN organs; action taken remains institution- and Charter-dependent"
  false refl

------------------------------------------------------------------------
-- "No teeth" decomposition.
------------------------------------------------------------------------

data TeethCoordinate : Set where
  normativeObligation
  adjudicativeAuthority
  interimBindingOrder
  punitiveJurisdiction
  coerciveExecutionArm
  politicalEnforcementActuator
  domesticImplementationCapacity
  : TeethCoordinate

data CoordinateState : Set where
  present
  conditional
  externallyDependent
  absentAtForum
  : CoordinateState

icjTeethState : TeethCoordinate → CoordinateState
icjTeethState normativeObligation = present
icjTeethState adjudicativeAuthority = conditional
icjTeethState interimBindingOrder = conditional
icjTeethState punitiveJurisdiction = absentAtForum
icjTeethState coerciveExecutionArm = absentAtForum
icjTeethState politicalEnforcementActuator = externallyDependent
icjTeethState domesticImplementationCapacity = externallyDependent

record NoTeethDecomposition : Set where
  constructor no-teeth-decomposition
  field
    bindingLawPresent : Bool
    bindingLawPresentIsTrue : bindingLawPresent ≡ true
    bindingJudgmentPossible : Bool
    bindingJudgmentPossibleIsTrue : bindingJudgmentPossible ≡ true
    icjHasOwnPoliceOrSheriffArm : Bool
    icjHasOwnPoliceOrSheriffArmIsFalse : icjHasOwnPoliceOrSheriffArm ≡ false
    enforcementCanDependOnSecurityCouncil : Bool
    enforcementCanDependOnSecurityCouncilIsTrue : enforcementCanDependOnSecurityCouncil ≡ true
    securityCouncilActionAutomatic : Bool
    securityCouncilActionAutomaticIsFalse : securityCouncilActionAutomatic ≡ false
    substantiveCouncilActionCanBeVetoBlocked : Bool
    substantiveCouncilActionCanBeVetoBlockedIsTrue : substantiveCouncilActionCanBeVetoBlocked ≡ true
    domesticImplementationStillMatters : Bool
    domesticImplementationStillMattersIsTrue : domesticImplementationStillMatters ≡ true

open NoTeethDecomposition public

canonicalNoTeethDecomposition : NoTeethDecomposition
canonicalNoTeethDecomposition = no-teeth-decomposition
  true refl
  true refl
  false refl
  true refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- Source-attribution pins.
------------------------------------------------------------------------

sourceAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority Sources.genocideEnforcementAtlas ≡ false
sourceAtlasDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ICJHasNoTeethMeansICJJudgmentsAreNonBinding : Set where
data BindingJudgmentMeansSelfExecutingCoercion : Set where
data ICJCanPunishIndividualsCriminally : Set where
data SecurityCouncilRecourseGuaranteesEnforcement : Set where
data GenocideClassificationAutomaticallySelectsEnforcementRoute : Set where
data ProvisionalMeasuresAutomaticallyResolveMerits : Set where

noTeethDoesNotMeanNonBinding : ICJHasNoTeethMeansICJJudgmentsAreNonBinding → ⊥
noTeethDoesNotMeanNonBinding ()

bindingDoesNotMeanSelfExecuting : BindingJudgmentMeansSelfExecutingCoercion → ⊥
bindingDoesNotMeanSelfExecuting ()

icjIsNotIndividualCriminalTribunal : ICJCanPunishIndividualsCriminally → ⊥
icjIsNotIndividualCriminalTribunal ()

securityCouncilRouteDoesNotGuaranteeCompliance :
  SecurityCouncilRecourseGuaranteesEnforcement → ⊥
securityCouncilRouteDoesNotGuaranteeCompliance ()

classificationDoesNotAutoSelectMeans :
  GenocideClassificationAutomaticallySelectsEnforcementRoute → ⊥
classificationDoesNotAutoSelectMeans ()

provisionalMeasuresDoNotResolveMerits :
  ProvisionalMeasuresAutomaticallyResolveMerits → ⊥
provisionalMeasuresDoNotResolveMerits ()
