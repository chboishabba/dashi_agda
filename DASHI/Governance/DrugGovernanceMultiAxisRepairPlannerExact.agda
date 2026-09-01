module DASHI.Governance.DrugGovernanceMultiAxisRepairPlannerExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Governance.DrugGovernanceMultiAxisReparativeFibreExact as Fibre
import DASHI.Governance.DrugGovernanceRepairMandateGateExact as Mandate

------------------------------------------------------------------------
-- MULTI-AXIS BIDI REPAIR PLANNER
--
-- A repair consumer asks one axis at a time.  The next observation is the
-- minimal probe for that axis, not a demand to reconstruct every historical or
-- political coordinate at once.
------------------------------------------------------------------------

data RepairConsumer : Set where
  acknowledgementConsumer
  truthHistoryConsumer
  materialRepairConsumer
  institutionalReformConsumer
  categoryAuthorityConsumer
  decisionRightsConsumer
  sovereigntyRepairConsumer
  nonRepetitionConsumer
  : RepairConsumer

consumerAxis : RepairConsumer → Fibre.DrugRepairAxis
consumerAxis acknowledgementConsumer = Fibre.acknowledgementAxis
consumerAxis truthHistoryConsumer = Fibre.truthHistoryAxis
consumerAxis materialRepairConsumer = Fibre.materialRestitutionBenefitAxis
consumerAxis institutionalReformConsumer = Fibre.institutionalReformAxis
consumerAxis categoryAuthorityConsumer = Fibre.categoryAuthorityRestorationAxis
consumerAxis decisionRightsConsumer = Fibre.decisionRightsAxis
consumerAxis sovereigntyRepairConsumer = Fibre.sovereignAuthorityAxis
consumerAxis nonRepetitionConsumer = Fibre.nonRepetitionAxis

repairObserver : RepairConsumer → Fibre.DrugReparativeFibre → Fibre.DrugRepairStatus
repairObserver consumer fibre = Fibre.status fibre (consumerAxis consumer)

probeFor : RepairConsumer → Discriminator.ExperimentBundle Fibre.DrugReparativeFibre
probeFor consumer = Discriminator.experimentBundle
  Fibre.DrugRepairStatus
  (repairObserver consumer)
  1
  "single-axis reparative probe"
  "reports only the declared repair axis; no whole-history reconstruction implied"

------------------------------------------------------------------------
-- Concrete live collisions.
------------------------------------------------------------------------

truthProbeSeparatesAcknowledgementFromFullRepair :
  Discriminator.BundleSeparates
    (probeFor truthHistoryConsumer)
    Fibre.acknowledgementOnly
    Fibre.fullSyntheticRepair
truthProbeSeparatesAcknowledgementFromFullRepair =
  Discriminator.bundleSeparates (λ ())

materialProbeSeparatesAcknowledgementFromMaterialRepair :
  Discriminator.BundleSeparates
    (probeFor materialRepairConsumer)
    Fibre.acknowledgementOnly
    Fibre.materialBenefitOnly
materialProbeSeparatesAcknowledgementFromMaterialRepair =
  Discriminator.bundleSeparates (λ ())

sovereigntyProbeSeparatesAuthorityReformFromFullRepair :
  Discriminator.BundleSeparates
    (probeFor sovereigntyRepairConsumer)
    Fibre.authorityReformWithoutSovereignty
    Fibre.fullSyntheticRepair
sovereigntyProbeSeparatesAuthorityReformFromFullRepair =
  Discriminator.bundleSeparates (λ ())

nonRepetitionProbeSeparatesAuthorityReformFromFullRepair :
  Discriminator.BundleSeparates
    (probeFor nonRepetitionConsumer)
    Fibre.authorityReformWithoutSovereignty
    Fibre.fullSyntheticRepair
nonRepetitionProbeSeparatesAuthorityReformFromFullRepair =
  Discriminator.bundleSeparates (λ ())

------------------------------------------------------------------------
-- Backward admission demands remain independent from diagnostic closure.
------------------------------------------------------------------------

data RepairActuationDemand : RepairConsumer → Set where
  categoryAuthorityNeedsMetaRuleAuthority :
    RepairActuationDemand categoryAuthorityConsumer
  materialRepairNeedsMaterialGovernanceAuthority :
    RepairActuationDemand materialRepairConsumer
  sovereigntyRepairNeedsOriginatingAuthority :
    RepairActuationDemand sovereigntyRepairConsumer
  institutionalReformNeedsScopedAuthority :
    RepairActuationDemand institutionalReformConsumer
  decisionRightsRepairNeedsDecisionAuthority :
    RepairActuationDemand decisionRightsConsumer
  nonRepetitionNeedsImplementationAuthority :
    RepairActuationDemand nonRepetitionConsumer
  truthHistoryNeedsEvidenceAuthority :
    RepairActuationDemand truthHistoryConsumer
  acknowledgementNeedsAcknowledgementAuthority :
    RepairActuationDemand acknowledgementConsumer

sovereigntyRepairDemand : RepairActuationDemand sovereigntyRepairConsumer
sovereigntyRepairDemand = sovereigntyRepairNeedsOriginatingAuthority

materialRepairDemand : RepairActuationDemand materialRepairConsumer
materialRepairDemand = materialRepairNeedsMaterialGovernanceAuthority

existingSovereigntyMandateDemand :
  Mandate.RepairAdmissionDemand Mandate.restoreSovereignAuthorityGate
existingSovereigntyMandateDemand = Mandate.sovereigntyRepairNeedsOriginatingAuthority

existingMaterialMandateDemand :
  Mandate.RepairAdmissionDemand Mandate.reviseBenefitRouting
existingMaterialMandateDemand = Mandate.benefitRevisionNeedsMaterialGovernanceAuthority

------------------------------------------------------------------------
-- Minimality is consumer-relative: solving one repair consumer does not close
-- the others.
------------------------------------------------------------------------

materialRepairStillLeavesSovereigntyOpen :
  repairObserver sovereigntyRepairConsumer Fibre.materialBenefitOnly
  ≡ Fibre.repairedRepair → ⊥
materialRepairStillLeavesSovereigntyOpen ()

acknowledgementStillLeavesTruthOpen :
  repairObserver truthHistoryConsumer Fibre.acknowledgementOnly
  ≡ Fibre.repairedRepair → ⊥
acknowledgementStillLeavesTruthOpen ()

authorityRepairStillLeavesNonRepetitionOpen :
  repairObserver nonRepetitionConsumer Fibre.authorityReformWithoutSovereignty
  ≡ Fibre.repairedRepair → ⊥
authorityRepairStillLeavesNonRepetitionOpen ()

data ProbeResolutionPromotesMandate : Set where

data OneConsumerClosurePromotesAllRepairClosure : Set where

probeResolutionDoesNotPromoteMandate : ProbeResolutionPromotesMandate → ⊥
probeResolutionDoesNotPromoteMandate ()

oneConsumerClosureDoesNotPromoteAllRepairClosure : OneConsumerClosurePromotesAllRepairClosure → ⊥
oneConsumerClosureDoesNotPromoteAllRepairClosure ()

record MultiAxisRepairPlannerBoundary : Set where
  constructor multiAxisRepairPlannerBoundary
  field
    oneAxisAtATimeIsAllowed : Bool
    oneAxisAtATimeIsAllowedIsTrue : oneAxisAtATimeIsAllowed ≡ true
    probeResolutionCreatesMandate : Bool
    probeResolutionCreatesMandateIsFalse : probeResolutionCreatesMandate ≡ false
    oneRepairConsumerClosesAllAxes : Bool
    oneRepairConsumerClosesAllAxesIsFalse : oneRepairConsumerClosesAllAxes ≡ false
    sovereigntyBackpropagatesToOriginatingAuthority : Bool
    sovereigntyBackpropagatesToOriginatingAuthorityIsTrue :
      sovereigntyBackpropagatesToOriginatingAuthority ≡ true

canonicalMultiAxisRepairPlannerBoundary : MultiAxisRepairPlannerBoundary
canonicalMultiAxisRepairPlannerBoundary =
  multiAxisRepairPlannerBoundary true refl false refl false refl true refl
