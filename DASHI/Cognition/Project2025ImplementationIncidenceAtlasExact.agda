module DASHI.Cognition.Project2025ImplementationIncidenceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Systemic

------------------------------------------------------------------------
-- PROJECT 2025: CHAPTER -> AUTHOR -> OFFICE -> ACTION -> INCIDENCE
--
-- This owner upgrades generic policy-overlap claims to typed correspondences.
-- A correspondence is evidence of implementation continuity, not automatic
-- proof that Project 2025 caused the action, that every chapter was adopted, or
-- that a beneficiary caused or requested the policy.
------------------------------------------------------------------------

data ImplementationDomain : Set where
  executiveOfficeOMB : ImplementationDomain
  civilService : ImplementationDomain
  federalCommunications : ImplementationDomain
  mediaOwnership : ImplementationDomain
  agencyCapacity : ImplementationDomain

record AuthorRoleActionReceipt : Set where
  constructor author-role-action-receipt
  field
    domain : ImplementationDomain
    chapterOrProjectRole : String
    namedActor : String
    administrationRole : String
    laterAction : String
    sourceBasis : String
    authorRolePaid : Bool
    administrationRolePaid : Bool
    actionPaid : Bool
    recommendationActionMatchPaid : Bool
    projectCausationPaid : Bool
open AuthorRoleActionReceipt public

voughtOMBReceipt : AuthorRoleActionReceipt
voughtOMBReceipt = author-role-action-receipt
  executiveOfficeOMB
  "Project 2025 Mandate for Leadership, Chapter 2: Executive Office of the President of the United States"
  "Russ Vought"
  "Director, Office of Management and Budget in the second Trump administration"
  "OMB-centered administrative restructuring, spending/control initiatives and civil-service changes"
  "Heritage Project 2025 author list; appointment records; Reuters implementation reporting"
  true true true true false

scheduleFReceipt : AuthorRoleActionReceipt
scheduleFReceipt = author-role-action-receipt
  civilService
  "Project 2025 personnel/executive-control architecture and Vought-associated transition planning"
  "Russ Vought / administration personnel apparatus"
  "OMB and executive-branch implementation roles"
  "2026 rule removing traditional job protections from up to roughly 50,000 policy-influencing federal employees"
  "Reuters 2026 civil-service reporting; Project 2025 personnel/administrative-state materials"
  true true true true false

carrFCCReceipt : AuthorRoleActionReceipt
carrFCCReceipt = author-role-action-receipt
  federalCommunications
  "Project 2025 Mandate for Leadership, Chapter 28: Federal Communications Commission"
  "Brendan Carr"
  "Chair, Federal Communications Commission"
  "FCC deregulatory and media-ownership agenda under Carr"
  "Heritage/Project 2025 chapter attribution; FCC appointment; Reuters/FCC records"
  true true true true false

mediaOwnershipReceipt : AuthorRoleActionReceipt
mediaOwnershipReceipt = author-role-action-receipt
  mediaOwnership
  "Chapter 28 recommends review/rescission of media-ownership regulations it characterises as outdated"
  "Brendan Carr"
  "FCC Chair"
  "2026 FCC action repealing the 39 percent national television ownership cap in favor of case-by-case review"
  "Project 2025 FCC chapter; FCC 2026 rulemaking; Reuters 2026 reporting"
  true true true true false

nexstarTegnaReceipt : AuthorRoleActionReceipt
nexstarTegnaReceipt = author-role-action-receipt
  mediaOwnership
  "Project 2025 FCC deregulatory/media-ownership policy surface"
  "Brendan Carr"
  "FCC Chair"
  "FCC approval of Nexstar's approximately USD 3.54b acquisition of Tegna, expanding the combined broadcaster's reach to about 80 percent of US TV households subject to the reported conditions/waivers"
  "Reuters 2026 transaction/regulatory reporting"
  true true true false false

record IncidenceReceipt : Set where
  constructor incidence-receipt
  field
    domain : ImplementationDomain
    firstOrderBeneficiary : String
    firstOrderBurdenBearer : String
    secondOrderQuestion : String
    thirdOrderQuestion : String
    benefitPaid : Bool
    burdenPaid : Bool
    netWelfareResolved : Bool
open IncidenceReceipt public

civilServiceIncidence : IncidenceReceipt
civilServiceIncidence = incidence-receipt
  civilService
  "President and political appointees gain greater formal removal/control capacity over covered policy-influencing positions"
  "covered federal employees lose prior job-protection status; reported litigation/union opposition remains separately sourced"
  "Does easier removal change implementation speed, dissent, whistleblowing, expertise retention or appointment leverage?"
  "Does altered workforce composition create durable path dependence in institutional memory, policy capacity and successor-administration reversibility?"
  true true false

mediaOwnershipIncidence : IncidenceReceipt
mediaOwnershipIncidence = incidence-receipt
  mediaOwnership
  "broadcast owners seeking transactions above the former national cap gain additional consolidation option value subject to case-by-case FCC approval"
  "no universal burden is source-paid merely from repeal; critics allege concentration/local-independence risks that require outcome-specific measurement"
  "Which transactions, financing structures, advertisers and owners capture value from the relaxed constraint?"
  "Does consolidation alter editorial diversity, bargaining power, local journalism, political advertising reach or future entry/exit?"
  true false false

nexstarIncidence : IncidenceReceipt
nexstarIncidence = incidence-receipt
  mediaOwnership
  "Nexstar/Tegna transaction receives regulatory approval and enlarged national reach"
  "competitor/public/local-editorial burdens are disputed and require separate evidence"
  "How do expanded reach, retransmission leverage and advertising inventory change firm/competitor bargaining positions?"
  "Does ownership concentration change national/local information topology or political-message distribution over time?"
  true false false

record Project2025IncidenceBoundary : Set where
  constructor project2025-incidence-boundary
  field
    chapterAuthorRoleActionChainsPaid : Bool
    civilServiceControlIncidencePaid : Bool
    mediaOwnershipOptionValuePaid : Bool
    specificNexstarApprovalPaid : Bool
    project2025CausedEveryMatchedAction : Bool
    deregulationEqualsNetSocialBenefit : Bool
    consolidationEqualsCensorship : Bool
    personnelControlEqualsIllegalPurge : Bool
open Project2025IncidenceBoundary public

canonicalProject2025IncidenceBoundary : Project2025IncidenceBoundary
canonicalProject2025IncidenceBoundary = project2025-incidence-boundary
  true true true true false false false false

project2025ThirdOrderCandidate : Systemic.SystemicLeverageCandidate
project2025ThirdOrderCandidate = Systemic.systemic-leverage-candidate
  "Project 2025 chapter-author-office-action incidence"
  Systemic.thirdOrder
  Systemic.institutionalControl
  "Which matched recommendations become durable changes to personnel authority, regulatory constraints, market structure or information infrastructure?"
  "Which office-holders, firms, constituencies or intermediaries gain durable option value or bargaining power?"
  "Which workers, competitors, communities, publics or future administrations bear deferred burdens or reduced reversibility?"
  "Who controls the new rule/appointment/market state, who can challenge it, and who retains practical exit?"
  "chapter-level text, appointment records, final rules/orders, transaction records, litigation and longitudinal outcome measures"
  true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RecommendationMatchImpliesCausation : Set where
data BeneficiaryImpliesPolicySponsor : Set where
data DeregulationImpliesBenefit : Set where
data ConsolidationImpliesInformationControl : Set where
data CivilServiceControlImpliesIllegality : Set where

recommendationMatchDoesNotCreateCausation : RecommendationMatchImpliesCausation → ⊥
recommendationMatchDoesNotCreateCausation ()

beneficiaryDoesNotCreatePolicySponsor : BeneficiaryImpliesPolicySponsor → ⊥
beneficiaryDoesNotCreatePolicySponsor ()

deregulationDoesNotCreateNetBenefit : DeregulationImpliesBenefit → ⊥
deregulationDoesNotCreateNetBenefit ()

consolidationDoesNotCreateInformationControl : ConsolidationImpliesInformationControl → ⊥
consolidationDoesNotCreateInformationControl ()

civilServiceControlDoesNotCreateIllegality : CivilServiceControlImpliesIllegality → ⊥
civilServiceControlDoesNotCreateIllegality ()
