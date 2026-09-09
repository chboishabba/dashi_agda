module DASHI.Law.SensibLawWoogarooDecisionMakerAndDelayLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WOOGAROO DECISION-MAKER / REPRESENTATIVE / DELAY LINEAGE
--
-- Keeps separate:
--   * statutory decision-maker;
--   * electorate representative;
--   * portfolio minister asked to advocate;
--   * campaign contact target;
--   * sourced procedural deadline/delay.
--
-- A politician appearing in campaign correspondence does not by itself make
-- that person the legal approver for every Woogaroo project.
------------------------------------------------------------------------

data PoliticalRole : Set where
  commonwealthEPBCDecisionMaker : PoliticalRole
  federalElectorateRepresentative : PoliticalRole
  stateElectorateRepresentative : PoliticalRole
  queenslandEnvironmentPortfolioMinister : PoliticalRole
  campaignAdvocacyTarget : PoliticalRole

data PersonRef : Set where
  murrayWatt : PersonRef
  miltonDick : PersonRef
  shayneNeumann : PersonRef
  charisMullen : PersonRef
  andrewPowell : PersonRef

record PoliticalRoleReceipt : Set where
  constructor political-role-receipt
  field
    person : PersonRef
    role : PoliticalRole
    boundedDescription : String
    primaryOrOfficialSource : String
    sourcePaid : Bool

open PoliticalRoleReceipt public

murrayWattEPBCPortfolioReceipt : PoliticalRoleReceipt
murrayWattEPBCPortfolioReceipt = political-role-receipt
  murrayWatt
  commonwealthEPBCDecisionMaker
  "Senator the Hon Murray Watt is the Commonwealth Minister for the Environment and Water; Woogaroo EPBC advocacy and current campaign material routes the federal approval/refusal request to that portfolio."
  "DCCEEW Ministers website; Save Woogaroo Forest action page"
  true

miltonDickRepresentativeReceipt : PoliticalRoleReceipt
miltonDickRepresentativeReceipt = political-role-receipt
  miltonDick
  federalElectorateRepresentative
  "Milton Dick is listed by the campaign as a federal representative to contact in relation to Woogaroo matters affecting the Oxley area."
  "Save Woogaroo Forest action page"
  true

shayneNeumannRepresentativeReceipt : PoliticalRoleReceipt
shayneNeumannRepresentativeReceipt = political-role-receipt
  shayneNeumann
  federalElectorateRepresentative
  "Shayne Neumann is listed by the campaign as a federal representative to contact in relation to Woogaroo matters affecting the Blair area."
  "Save Woogaroo Forest action page"
  true

charisMullenRepresentativeReceipt : PoliticalRoleReceipt
charisMullenRepresentativeReceipt = political-role-receipt
  charisMullen
  stateElectorateRepresentative
  "Charis Mullen is listed by the campaign as the State Member for Jordan to contact regarding Woogaroo."
  "Save Woogaroo Forest action page"
  true

andrewPowellPortfolioReceipt : PoliticalRoleReceipt
andrewPowellPortfolioReceipt = political-role-receipt
  andrewPowell
  queenslandEnvironmentPortfolioMinister
  "Andrew Powell is listed by the campaign as the Queensland Environment Minister to contact regarding Woogaroo."
  "Save Woogaroo Forest action page"
  true

------------------------------------------------------------------------
-- WrongType firewalls for political role.
------------------------------------------------------------------------

data LocalMemberEqualsStatutoryApprover : Set where
data CampaignContactTargetEqualsLegalDecisionMaker : Set where
data EnvironmentPortfolioEqualsParcelElectorateRepresentation : Set where

localMemberDoesNotBecomeApproverByRole : LocalMemberEqualsStatutoryApprover → ⊥
localMemberDoesNotBecomeApproverByRole ()

campaignTargetDoesNotBecomeDecisionMaker : CampaignContactTargetEqualsLegalDecisionMaker → ⊥
campaignTargetDoesNotBecomeDecisionMaker ()

portfolioDoesNotDetermineElectorate : EnvironmentPortfolioEqualsParcelElectorateRepresentation → ⊥
portfolioDoesNotDetermineElectorate ()

------------------------------------------------------------------------
-- Delay/deadline provenance.
------------------------------------------------------------------------

data DelayStatus : Set where
  exactFirstOctober2026DeadlineSourceOpen : DelayStatus
  sourcePaidProceduralDelay : DelayStatus

record DelayReceipt : Set where
  constructor delay-receipt
  field
    status : DelayStatus
    assertedDate : String
    projectOrDecision : String
    sourceReference : String
    sourcePaid : Bool
    protectionCreated : Bool

open DelayReceipt public

firstOctober2026Lead : DelayReceipt
firstOctober2026Lead = delay-receipt
  exactFirstOctober2026DeadlineSourceOpen
  "1 October 2026"
  "Woogaroo-related federal/project decision or procedural deadline — exact project and instrument not yet recovered by this owner"
  "user/campaign lead pending primary-source acquisition"
  false
  false

record DecisionMakerDelayBoundary : Set where
  constructor decision-maker-delay-boundary
  field
    murrayWattNameResolved : Bool
    murrayWattIsFederalEnvironmentMinister : Bool
    localRepresentationSeparatedFromApprovalPower : Bool
    firstOctoberDateRequiresPrimarySource : Bool
    delayCreatesProtection : Bool

canonicalDecisionMakerDelayBoundary : DecisionMakerDelayBoundary
canonicalDecisionMakerDelayBoundary =
  decision-maker-delay-boundary true true true true false
