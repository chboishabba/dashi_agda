module DASHI.Law.SensibLawWoogarooDecisionMakerAndDelayLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WOOGAROO DECISION-MAKER / REPRESENTATIVE / DELAY LINEAGE
--
-- Keeps separate:
--   * authorised statutory delegate for the particular EPBC decision;
--   * Commonwealth Environment portfolio minister;
--   * electorate representative;
--   * Queensland portfolio minister;
--   * campaign advocacy target;
--   * sourced procedural deadline/delay.
--
-- A politician appearing in campaign correspondence does not by itself make
-- that person the legal approver for the particular controlled action.
------------------------------------------------------------------------

data PoliticalRole : Set where
  commonwealthEPBCAuthorisedDelegate : PoliticalRole
  commonwealthEnvironmentPortfolioMinister : PoliticalRole
  federalElectorateRepresentative : PoliticalRole
  stateElectorateRepresentative : PoliticalRole
  queenslandEnvironmentPortfolioMinister : PoliticalRole
  campaignAdvocacyTarget : PoliticalRole

data PersonRef : Set where
  declanOConnorCox : PersonRef
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

declanOConnorCoxEPBC8575DelegateReceipt : PoliticalRoleReceipt
declanOConnorCoxEPBC8575DelegateReceipt = political-role-receipt
  declanOConnorCox
  commonwealthEPBCAuthorisedDelegate
  "The 2 September 2026 National Environmental Protection Agency notice for Springfield Residential Development, EPBC 2019/8575, names Declan O'Connor-Cox, Branch Head, Environment Assessments Queensland, as the person authorised to make the approval decision."
  "Australian Government National Environmental Protection Agency, Notification of extension to time in which to make a decision whether or not to approve a controlled action, EPBC 2019/8575, dated 2 September 2026"
  true

murrayWattEPBCPortfolioReceipt : PoliticalRoleReceipt
murrayWattEPBCPortfolioReceipt = political-role-receipt
  murrayWatt
  commonwealthEnvironmentPortfolioMinister
  "Senator the Hon Murray Watt is the Commonwealth Minister for the Environment and Water. This portfolio relationship is distinct from the particular delegation recorded for EPBC 2019/8575."
  "DCCEEW Ministers website"
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

data PortfolioMinisterEqualsAuthorisedDelegate : Set where
data LocalMemberEqualsStatutoryApprover : Set where
data CampaignContactTargetEqualsLegalDecisionMaker : Set where
data EnvironmentPortfolioEqualsParcelElectorateRepresentation : Set where

portfolioMinisterDoesNotEqualDelegateByRole :
  PortfolioMinisterEqualsAuthorisedDelegate → ⊥
portfolioMinisterDoesNotEqualDelegateByRole ()

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

springfieldEPBC8575FirstOctober2026Delay : DelayReceipt
springfieldEPBC8575FirstOctober2026Delay = delay-receipt
  sourcePaidProceduralDelay
  "1 October 2026"
  "Springfield Residential Development, Springfield, Queensland — EPBC 2019/8575 — deadline for decision whether or not to approve the controlled action"
  "Australian Government National Environmental Protection Agency, s 130(1A) notification dated 2 September 2026: relevant period extended by 20 business days to 1 October 2026"
  true
  false

------------------------------------------------------------------------
-- Exact procedural receipt.
------------------------------------------------------------------------

record EPBC130ExtensionReceipt : Set where
  constructor epbc130-extension-receipt
  field
    epbcReference : String
    proposedActionPerson : String
    proposedAction : String
    statutoryBasis : String
    extensionLength : String
    newDecisionDeadline : String
    authorisedDecisionMaker : PersonRef
    authorisedDecisionMakerPosition : String
    noticeDecisionDate : String
    sourcePaid : Bool
    extensionCreatesSubstantiveProtection : Bool

open EPBC130ExtensionReceipt public

springfield20198575ExtensionReceipt : EPBC130ExtensionReceipt
springfield20198575ExtensionReceipt = epbc130-extension-receipt
  "EPBC 2019/8575"
  "Cherish Enterprises Pty. Ltd. ACN 052 055 811"
  "To develop a residential subdivision in Springfield, Queensland"
  "Environment Protection and Biodiversity Conservation Act 1999 (Cth), s 130(1A); notice also states purposes of ss 130(1A), 130(1B) and 130(4)"
  "20 business days"
  "1 October 2026"
  declanOConnorCox
  "Branch Head, Environment Assessments Queensland"
  "2 September 2026"
  true
  false

record DecisionMakerDelayBoundary : Set where
  constructor decision-maker-delay-boundary
  field
    firstOctoberDateSourcePaid : Bool
    exactProjectResolved : Bool
    authorisedDelegateResolved : Bool
    murrayWattPortfolioSeparatedFromDelegate : Bool
    localRepresentationSeparatedFromApprovalPower : Bool
    delayCreatesProtection : Bool

canonicalDecisionMakerDelayBoundary : DecisionMakerDelayBoundary
canonicalDecisionMakerDelayBoundary =
  decision-maker-delay-boundary true true true true true false
