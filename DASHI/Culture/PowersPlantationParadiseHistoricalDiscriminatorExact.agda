module DASHI.Culture.PowersPlantationParadiseHistoricalDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical
import DASHI.Culture.PowersPlantationParadiseMinetteChronologyContestationExact as Chronology

------------------------------------------------------------------------
-- HISTORICAL DISCRIMINATOR DESIGN
--
-- Archive acquisition is driven by explicit competing propositions.  A
-- discriminator identifies an observation capable of changing the live claim
-- fibre; it does not create historical truth merely by being proposed.
------------------------------------------------------------------------

data HistoricalQuestion : Set where
  seatingRuleQuestion : HistoricalQuestion
  minetteSettlementQuestion : HistoricalQuestion
  july1790ChronologyQuestion : HistoricalQuestion
  actorDistributionQuestion : HistoricalQuestion

data HistoricalDiscriminator : Set where
  applicableOrdinance : HistoricalDiscriminator
  theatrePoliceRule : HistoricalDiscriminator
  seatPriceNotice : HistoricalDiscriminator
  enforcementIncident : HistoricalDiscriminator
  archiveOriginalPlan : HistoricalDiscriminator
  estateExecutorEntry : HistoricalDiscriminator
  benefitNightAccount : HistoricalDiscriminator
  exactAffichesIssueImage : HistoricalDiscriminator
  namedActorCompensationRecord : HistoricalDiscriminator
  namedActorGovernanceRecord : HistoricalDiscriminator

data CompetingInterpretation : HistoricalQuestion → Set where
  formalRulePrimary : CompetingInterpretation seatingRuleQuestion
  architectureCustomPrimary : CompetingInterpretation seatingRuleQuestion
  rulePracticeDivergence : CompetingInterpretation seatingRuleQuestion

  salarySettled : CompetingInterpretation minetteSettlementQuestion
  salaryRemainedUnsettled : CompetingInterpretation minetteSettlementQuestion
  settlementUnknown : CompetingInterpretation minetteSettlementQuestion

  july1NoticeDate : CompetingInterpretation july1790ChronologyQuestion
  july17NoticeDate : CompetingInterpretation july1790ChronologyQuestion
  multipleNoticeDates : CompetingInterpretation july1790ChronologyQuestion

  contributionWithMaterialBenefit : CompetingInterpretation actorDistributionQuestion
  contributionWithoutMaterialBenefit : CompetingInterpretation actorDistributionQuestion
  benefitIncidenceUnknown : CompetingInterpretation actorDistributionQuestion

record DiscriminatorRoute : Set where
  constructor discriminator-route
  field
    question : HistoricalQuestion
    discriminator : HistoricalDiscriminator
    sourceTarget : String
    distinguishes : String
    sameObjectRequirement : String
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open DiscriminatorRoute public

seatingOrdinanceRoute : DiscriminatorRoute
seatingOrdinanceRoute =
  discriminator-route
    seatingRuleQuestion
    applicableOrdinance
    "Saint-Domingue ordinance/police/theatre regulation with venue/date applicability"
    "formal rule versus architecture/custom-only explanations"
    "instrument, venue, date, governed class and applicability must be on the same object"
    false refl

seatingEnforcementRoute : DiscriminatorRoute
seatingEnforcementRoute =
  discriminator-route
    seatingRuleQuestion
    enforcementIncident
    "contemporaneous enforcement, complaint, police or court record"
    "written rule versus realised/enforced practice"
    "incident must retain venue/date/class/rule coordinates"
    false refl

minetteSettlementRoute : DiscriminatorRoute
minetteSettlementRoute =
  discriminator-route
    minetteSettlementQuestion
    estateExecutorEntry
    "Saint-Martin estate/executor account, payee receipt or creditor entry"
    "contracted arrears versus actual transfer/final settlement"
    "Minette, Saint-Martin estate, obligation and transfer must be joined by source provenance"
    false refl

july1790PrimaryIssueRoute : DiscriminatorRoute
july1790PrimaryIssueRoute =
  discriminator-route
    july1790ChronologyQuestion
    exactAffichesIssueImage
    "underlying July 1790 Affiches americaines issue/page/image"
    "1 July versus 17 July versus multiple-notice interpretations"
    "same notice proposition root and exact manifestation required"
    false refl

actorBenefitRoute : DiscriminatorRoute
actorBenefitRoute =
  discriminator-route
    actorDistributionQuestion
    namedActorCompensationRecord
    "named-person wage, benefit, account, transfer or contractual record"
    "contribution with material benefit versus contribution without recovered benefit"
    "actor identity, venue/time and payment relation must remain joined"
    false refl

actorVoiceRoute : DiscriminatorRoute
actorVoiceRoute =
  discriminator-route
    actorDistributionQuestion
    namedActorGovernanceRecord
    "named-person petition, complaint, contract negotiation, directorship or rule-making record"
    "productive contribution versus effective institutional voice"
    "actor identity and decision/contestability event must be on the same historical fibre"
    false refl

discriminatorScore : HistoricalDiscriminator → Nat
discriminatorScore applicableOrdinance = 9
discriminatorScore theatrePoliceRule = 9
discriminatorScore seatPriceNotice = 7
discriminatorScore enforcementIncident = 10
discriminatorScore archiveOriginalPlan = 6
discriminatorScore estateExecutorEntry = 10
discriminatorScore benefitNightAccount = 9
discriminatorScore exactAffichesIssueImage = 10
discriminatorScore namedActorCompensationRecord = 10
discriminatorScore namedActorGovernanceRecord = 10

data BetterHistoricalDiscriminator : HistoricalDiscriminator → HistoricalDiscriminator → Set where
  enforcementOverPlan : BetterHistoricalDiscriminator enforcementIncident archiveOriginalPlan
  executorOverBenefitLabel : BetterHistoricalDiscriminator estateExecutorEntry benefitNightAccount
  issueImageOverPriceNotice : BetterHistoricalDiscriminator exactAffichesIssueImage seatPriceNotice

powersHistoricalExperimentDesign :
  Robust.ExperimentDesign HistoricalDiscriminator Nat
powersHistoricalExperimentDesign =
  Robust.experimentDesign
    discriminatorScore
    BetterHistoricalDiscriminator
    ⊤

robustExperimentBoundary : Robust.RobustExperimentFrontierBoundary
robustExperimentBoundary = Robust.canonicalRobustExperimentFrontierBoundary

causalLeaf : Empirical.EmpiricalProgrammeLeaf
causalLeaf = Empirical.causalMobilityLeaf

chronologyRelation :
  Chronology.minette1790NoticeContestationRelation
  ≡ Chronology.minette1790NoticeContestationRelation
chronologyRelation = refl

data ProposedDiscriminatorCreatesHistoricalTruth : Set where

proposedDiscriminatorDoesNotCreateHistoricalTruth :
  ProposedDiscriminatorCreatesHistoricalTruth → ⊥
proposedDiscriminatorDoesNotCreateHistoricalTruth ()

record PowersHistoricalDiscriminatorBoundary : Set where
  constructor powers-historical-discriminator-boundary
  field
    acquisitionMayBeDrivenByCompetingInterpretations : Bool
    acquisitionMayBeDrivenByCompetingInterpretationsIsTrue :
      acquisitionMayBeDrivenByCompetingInterpretations ≡ true
    proposedDiscriminatorCreatesHistoricalTruth : Bool
    proposedDiscriminatorCreatesHistoricalTruthIsFalse :
      proposedDiscriminatorCreatesHistoricalTruth ≡ false
    architectureAloneEstablishesRule : Bool
    architectureAloneEstablishesRuleIsFalse :
      architectureAloneEstablishesRule ≡ false
    contractNonpaymentEstablishesFinalSettlement : Bool
    contractNonpaymentEstablishesFinalSettlementIsFalse :
      contractNonpaymentEstablishesFinalSettlement ≡ false
    secondaryDateDisagreementMayRemainOpenPendingPrimary : Bool
    secondaryDateDisagreementMayRemainOpenPendingPrimaryIsTrue :
      secondaryDateDisagreementMayRemainOpenPendingPrimary ≡ true

canonicalPowersHistoricalDiscriminatorBoundary : PowersHistoricalDiscriminatorBoundary
canonicalPowersHistoricalDiscriminatorBoundary =
  powers-historical-discriminator-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
