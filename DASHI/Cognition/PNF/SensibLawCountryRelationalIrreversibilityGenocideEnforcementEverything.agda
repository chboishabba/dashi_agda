module DASHI.Cognition.PNF.SensibLawCountryRelationalIrreversibilityGenocideEnforcementEverything where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawCountryRelationalIrreversibilityEverything as Country
import DASHI.Cognition.PNF.SensibLawCountryGenocideWrongTypeEnforcementEverything as GenocideEnforcement
import DASHI.Cognition.PNF.SensibLawGenocideConventionWrongTypeBidiExact as Wrong
import DASHI.Cognition.PNF.SensibLawGenocideEnforcementMeansBidiExact as Enforce

------------------------------------------------------------------------
-- Existing Country/relational irreversibility state remains primary.
------------------------------------------------------------------------

landCountryControlStillOpen :
  Country.Justice.currentOperationalJusticeState Country.Justice.landAndCountryControl
  ≡ Country.Justice.residualOpen
landCountryControlStillOpen = refl

compensationReparationStillOpen :
  Country.Justice.currentOperationalJusticeState Country.Justice.compensationAndReparation
  ≡ Country.Justice.residualOpen
compensationReparationStillOpen = refl

------------------------------------------------------------------------
-- Convention genocide is one WrongType fibre, not the universe of wrongs.
------------------------------------------------------------------------

conventionWrongTypeStatusForRelationalProbe :
  Wrong.classifyConventionWrongType
    (GenocideEnforcement.conventionElementState GenocideEnforcement.relationalLossConventionProbe)
  ≡ Wrong.conventionWrongTypeOpen
conventionWrongTypeStatusForRelationalProbe = refl

conventionMismatchDoesNotEraseRelationalWrong :
  Wrong.ConventionGenocideFailureMeansNoWrongOccurred → ⊥
conventionMismatchDoesNotEraseRelationalWrong = Wrong.conventionFailureDoesNotMeanNoWrong

------------------------------------------------------------------------
-- Reverse enforcement pins.
------------------------------------------------------------------------

stopConductRequiresProvisionalMeasuresPredicate :
  Enforce.firstRequiredPrerequisite Enforce.stopConductRoute
  ≡ Enforce.provisionalMeasuresJurisdictionAndPlausibilityReceipt
stopConductRequiresProvisionalMeasuresPredicate = refl

individualPunishmentRequiresCriminalForum :
  Enforce.firstRequiredPrerequisite Enforce.punishIndividualRoute
  ≡ Enforce.competentDomesticTribunalJurisdictionReceipt
individualPunishmentRequiresCriminalForum = refl

stateResponsibilityRequiresInterstateJurisdiction :
  Enforce.firstRequiredPrerequisite Enforce.stateResponsibilityRoute
  ≡ Enforce.interstateDisputeJurisdictionReceipt
stateResponsibilityRequiresInterstateJurisdiction = refl

postJudgmentCoercionBeginsFromNonCompliance :
  Enforce.firstRequiredPrerequisite Enforce.enforceJudgmentRoute
  ≡ Enforce.nonComplianceReceipt
postJudgmentCoercionBeginsFromNonCompliance = refl

------------------------------------------------------------------------
-- Precise "no teeth" state.
------------------------------------------------------------------------

bindingLawStillPresent :
  Enforce.bindingLawPresent Enforce.canonicalNoTeethDecomposition ≡ true
bindingLawStillPresent = refl

icjOwnExecutionArmStillAbsent :
  Enforce.icjHasOwnPoliceOrSheriffArm Enforce.canonicalNoTeethDecomposition ≡ false
icjOwnExecutionArmStillAbsent = refl

securityCouncilEnforcementStillNonAutomatic :
  Enforce.securityCouncilActionAutomatic Enforce.canonicalNoTeethDecomposition ≡ false
securityCouncilEnforcementStillNonAutomatic = refl

securityCouncilVetoRiskStillPresent :
  Enforce.substantiveCouncilActionCanBeVetoBlocked
    Enforce.canonicalNoTeethDecomposition ≡ true
securityCouncilVetoRiskStillPresent = refl

------------------------------------------------------------------------
-- Material justice remains the terminal consumer.
------------------------------------------------------------------------

data LegalClassificationEqualsRealisedRepair : Set where
data InternationalBindingOrderEqualsCountryRestoration : Set where

classificationDoesNotEqualRealisedRepair : LegalClassificationEqualsRealisedRepair → ⊥
classificationDoesNotEqualRealisedRepair ()

bindingOrderDoesNotEqualCountryRestoration : InternationalBindingOrderEqualsCountryRestoration → ⊥
bindingOrderDoesNotEqualCountryRestoration ()
