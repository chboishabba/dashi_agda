module DASHI.Culture.RastafariItalExitRefusalMarxUnionCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.MarxLabourUnionSourceBoundaryExact as MarxUnion
import DASHI.Culture.RastafariItalLoopControlGovernanceExact as Loop
import DASHI.Governance.OptionConeCoercionExact as OptionCone
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as SocioTechnical
import DASHI.Planning.CollectiveTerritorialConsentExact as Consent
import DASHI.Planning.ParticipatoryPlanningGovernanceExact as Participation

------------------------------------------------------------------------
-- EXIT / REFUSAL / CONTESTABILITY x MARX / UNIONISM
--
-- Repository-native cross-pollination owner.
--
-- Central separation:
--
--   participates
--   != can refuse
--   != can withdraw
--   != can change the rules
--   != has a viable material exit
--   != has collective organisation
--   != has effective bargaining power.
--
-- Marx and ILO C87/C98 supply bounded theoretical/normative source surfaces.
-- They do not prove the finite DASHI countermodels below, and no claim is made
-- that one finite labour carrier exhausts capitalism, unionism or Rastafari
-- social organisation.
------------------------------------------------------------------------

data ParticipationStatus : Set where
  participates doesNotParticipate : ParticipationStatus

data RefusalStatus : Set where
  refusalUnavailable refusalAvailable : RefusalStatus

data WithdrawalStatus : Set where
  withdrawalUnavailable withdrawalAvailable : WithdrawalStatus

data RuleChangeStatus : Set where
  noRuleChangePower consultRuleOnly collectiveRuleChange governingRuleChange
  : RuleChangeStatus

data MaterialExitStatus : Set where
  noViableMaterialExit fragileMaterialExit viableMaterialExit : MaterialExitStatus

data CollectiveOrganisationStatus : Set where
  noCollectiveOrganisation associationPresent independentOrganisation
  : CollectiveOrganisationStatus

data BargainingPowerStatus : Set where
  bargainingAbsent bargainingNominal bargainingEffective : BargainingPowerStatus

data DependenceStatus : Set where
  lowDependence highDependence : DependenceStatus

record ExitRefusalLabourState : Set where
  constructor exit-refusal-labour-state
  field
    participation : ParticipationStatus
    refusal : RefusalStatus
    withdrawal : WithdrawalStatus
    ruleChange : RuleChangeStatus
    materialExit : MaterialExitStatus
    collectiveOrganisation : CollectiveOrganisationStatus
    bargainingPower : BargainingPowerStatus
    dependence : DependenceStatus

open ExitRefusalLabourState public

------------------------------------------------------------------------
-- Same visible participation, very different option/control structures.
------------------------------------------------------------------------

participatingDependentNoVoice : ExitRefusalLabourState
participatingDependentNoVoice =
  exit-refusal-labour-state
    participates refusalUnavailable withdrawalUnavailable noRuleChangePower
    noViableMaterialExit noCollectiveOrganisation bargainingAbsent highDependence

participatingAssociationOnly : ExitRefusalLabourState
participatingAssociationOnly =
  exit-refusal-labour-state
    participates refusalAvailable withdrawalUnavailable consultRuleOnly
    fragileMaterialExit associationPresent bargainingNominal highDependence

participatingOrganisedBargaining : ExitRefusalLabourState
participatingOrganisedBargaining =
  exit-refusal-labour-state
    participates refusalAvailable withdrawalAvailable collectiveRuleChange
    viableMaterialExit independentOrganisation bargainingEffective lowDependence

participatingGovernor : ExitRefusalLabourState
participatingGovernor =
  exit-refusal-labour-state
    participates refusalAvailable withdrawalAvailable governingRuleChange
    viableMaterialExit independentOrganisation bargainingEffective lowDependence

------------------------------------------------------------------------
-- Participation cannot recover refusal/exit/governance fibres.
------------------------------------------------------------------------

participationCannotRecoverRefusal :
  NonFactor.FactorsThrough participation refusal → ⊥
participationCannotRecoverRefusal =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingDependentNoVoice participatingAssociationOnly refl (λ ()))

participationCannotRecoverWithdrawal :
  NonFactor.FactorsThrough participation withdrawal → ⊥
participationCannotRecoverWithdrawal =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingAssociationOnly participatingOrganisedBargaining refl (λ ()))

participationCannotRecoverRuleChange :
  NonFactor.FactorsThrough participation ruleChange → ⊥
participationCannotRecoverRuleChange =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingAssociationOnly participatingGovernor refl (λ ()))

participationCannotRecoverMaterialExit :
  NonFactor.FactorsThrough participation materialExit → ⊥
participationCannotRecoverMaterialExit =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingDependentNoVoice participatingOrganisedBargaining refl (λ ()))

participationCannotRecoverCollectiveOrganisation :
  NonFactor.FactorsThrough participation collectiveOrganisation → ⊥
participationCannotRecoverCollectiveOrganisation =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingDependentNoVoice participatingOrganisedBargaining refl (λ ()))

participationCannotRecoverBargainingPower :
  NonFactor.FactorsThrough participation bargainingPower → ⊥
participationCannotRecoverBargainingPower =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingAssociationOnly participatingOrganisedBargaining refl (λ ()))

------------------------------------------------------------------------
-- Even association/union-form participation cannot recover effective power.
------------------------------------------------------------------------

organisationCannotRecoverBargainingPower :
  NonFactor.FactorsThrough collectiveOrganisation bargainingPower → ⊥
organisationCannotRecoverBargainingPower =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingAssociationOnly
      (exit-refusal-labour-state
        participates refusalAvailable withdrawalUnavailable consultRuleOnly
        fragileMaterialExit associationPresent bargainingEffective highDependence)
      refl
      (λ ()))

refusalCannotRecoverMaterialExit :
  NonFactor.FactorsThrough refusal materialExit → ⊥
refusalCannotRecoverMaterialExit =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingAssociationOnly participatingOrganisedBargaining refl (λ ()))

withdrawalCannotRecoverRuleChange :
  NonFactor.FactorsThrough withdrawal ruleChange → ⊥
withdrawalCannotRecoverRuleChange =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      participatingOrganisedBargaining participatingGovernor refl (λ ()))

------------------------------------------------------------------------
-- Existing canonical governance theorems reused directly.
------------------------------------------------------------------------

participationStillDoesNotCreatePowerToRefuse :
  Consent.ConsentPromotionBoundary.participationImpliesPowerToRefuse
    Consent.canonicalConsentPromotionBoundary ≡ false
participationStillDoesNotCreatePowerToRefuse = refl

reviewOnlyStillNotWithdrawalPower :
  Consent.CollectiveConsentEnvelope.contestability Consent.consultationOnly
  ≡ Consent.canWithdraw → ⊥
reviewOnlyStillNotWithdrawalPower = Consent.reviewOnlyIsNotWithdrawalPower

recognisedLabourOppositionStillDoesNotOwnMetaRule :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
recognisedLabourOppositionStillDoesNotOwnMetaRule =
  Opposition.recognisedOppositionCannotAutomaticallyAlterRule

labourOppositionExteriorStillExists : Opposition.BoundedOppositionWitness
labourOppositionExteriorStillExists =
  Opposition.canonicalBoundedOpposition Opposition.labourDomain

coDecisionStillNotGoverning :
  Participation.stageLevel Participation.coDecidingStage ≡
  Participation.stageLevel Participation.governingStage → ⊥
coDecisionStillNotGoverning = Participation.coDecidingIsNotDefinitionallyGoverning

------------------------------------------------------------------------
-- Option-cone / material-exit cross-pollination.
------------------------------------------------------------------------

coerciveSystemStillRequiresLostSafeOption :
  OptionCone.StrictSafeReachabilityContraction
    OptionCone.demoReachability
    OptionCone.beforeResponse
    OptionCone.coerciveOutcome
coerciveSystemStillRequiresLostSafeOption =
  OptionCone.canonicalCoerciveReachabilityContraction

marketLabelStillCannotRecoverMaterialExitCone :
  NonFactor.FactorsThrough
    SocioTechnical.marketEconomyLabel
    SocioTechnical.materialExitCone → ⊥
marketLabelStillCannotRecoverMaterialExitCone =
  SocioTechnical.marketLabelCannotRecoverExitCone

labourParticipationStillCannotRecoverPoliticalVoice :
  NonFactor.FactorsThrough
    SocioTechnical.labourParticipation
    SocioTechnical.politicalVoice → ⊥
labourParticipationStillCannotRecoverPoliticalVoice =
  SocioTechnical.labourParticipationCannotRecoverPoliticalVoice

------------------------------------------------------------------------
-- Link to the existing circular-loop control topology.
------------------------------------------------------------------------

loopParticipationStillDoesNotRecoverDecisionRights :
  NonFactor.FactorsThrough Loop.contribution Loop.decision → ⊥
loopParticipationStillDoesNotRecoverDecisionRights =
  Loop.participationCannotRecoverDecisionRights

------------------------------------------------------------------------
-- Source-bounded Marx / unionism weld.
------------------------------------------------------------------------

marxLabourUnionSourceBoundary : MarxUnion.MarxLabourUnionSourceBoundary
marxLabourUnionSourceBoundary = MarxUnion.canonicalMarxLabourUnionSourceBoundary

marxSourceStillDoesNotProveControlTopology :
  MarxUnion.MarxSourceProvesDASHIControlTopology → ⊥
marxSourceStillDoesNotProveControlTopology =
  MarxUnion.marxSourceDoesNotProveDASHIControlTopology

freedomOfAssociationStillDoesNotEqualMaterialExit :
  MarxUnion.FreedomOfAssociationEqualsMaterialExit → ⊥
freedomOfAssociationStillDoesNotEqualMaterialExit =
  MarxUnion.freedomOfAssociationDoesNotEqualMaterialExit

collectiveBargainingStillDoesNotEqualMetaRuleAuthority :
  MarxUnion.CollectiveBargainingEqualsMetaRuleAuthority → ⊥
collectiveBargainingStillDoesNotEqualMetaRuleAuthority =
  MarxUnion.collectiveBargainingDoesNotEqualMetaRuleAuthority

------------------------------------------------------------------------
-- Explicit no-promotions.
------------------------------------------------------------------------

data ParticipationMeansFreeLabourRelation : Set where

data UnionPresenceMeansEffectiveBargaining : Set where

data RefusalRightMeansViableExit : Set where

data WithdrawalRightMeansRuleChangePower : Set where

data CircularSystemMeansWorkerControlledSystem : Set where

data CapitalismLabelDeterminesExitCone : Set where

data UnionismLabelDeterminesGovernanceTopology : Set where

participationDoesNotProveFreeLabourRelation :
  ParticipationMeansFreeLabourRelation → ⊥
participationDoesNotProveFreeLabourRelation ()

unionPresenceDoesNotProveEffectiveBargaining :
  UnionPresenceMeansEffectiveBargaining → ⊥
unionPresenceDoesNotProveEffectiveBargaining ()

refusalRightDoesNotProveViableExit : RefusalRightMeansViableExit → ⊥
refusalRightDoesNotProveViableExit ()

withdrawalRightDoesNotProveRuleChangePower : WithdrawalRightMeansRuleChangePower → ⊥
withdrawalRightDoesNotProveRuleChangePower ()

circularSystemDoesNotProveWorkerControl : CircularSystemMeansWorkerControlledSystem → ⊥
circularSystemDoesNotProveWorkerControl ()

capitalismLabelDoesNotDetermineExitCone : CapitalismLabelDeterminesExitCone → ⊥
capitalismLabelDoesNotDetermineExitCone ()

unionismLabelDoesNotDetermineGovernanceTopology :
  UnionismLabelDeterminesGovernanceTopology → ⊥
unionismLabelDoesNotDetermineGovernanceTopology ()

record ItalExitRefusalMarxUnionBoundary : Set where
  constructor ital-exit-refusal-marx-union-boundary
  field
    participationEqualsRefusalPower : Bool
    participationEqualsRefusalPowerIsFalse : participationEqualsRefusalPower ≡ false

    refusalEqualsWithdrawalPower : Bool
    refusalEqualsWithdrawalPowerIsFalse : refusalEqualsWithdrawalPower ≡ false

    withdrawalEqualsRuleChangePower : Bool
    withdrawalEqualsRuleChangePowerIsFalse : withdrawalEqualsRuleChangePower ≡ false

    formalAssociationEqualsEffectiveBargaining : Bool
    formalAssociationEqualsEffectiveBargainingIsFalse :
      formalAssociationEqualsEffectiveBargaining ≡ false

    formalRightsEqualMaterialExit : Bool
    formalRightsEqualMaterialExitIsFalse : formalRightsEqualMaterialExit ≡ false

    sourceAttributionSurvivesCrossPollination : Bool
    sourceAttributionSurvivesCrossPollinationIsTrue :
      sourceAttributionSurvivesCrossPollination ≡ true

canonicalItalExitRefusalMarxUnionBoundary : ItalExitRefusalMarxUnionBoundary
canonicalItalExitRefusalMarxUnionBoundary =
  ital-exit-refusal-marx-union-boundary
    false refl false refl false refl false refl false refl true refl
