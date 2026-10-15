module DASHI.Cognition.EpsteinFinancialSystemicPareto20261015Round3Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialSystemicPareto20261014Round2Exact as Prior
import DASHI.Cognition.EpsteinValarInvestmentLifecycle20261015Exact as ValarLifecycle
import DASHI.Cognition.EpsteinBlackEstatePlanningTransmission20261015Exact as BlackWork
import DASHI.Cognition.EpsteinWexnerChildrenTrustCapitalMesh20261015Exact as WexnerMesh
import DASHI.Cognition.EpsteinWexnerCOUQFungibleCapitalLifecycle20261015Exact as COUQ
import DASHI.Cognition.EpsteinWexnerTrustBearInvestmentAuthority20261015Exact as WexnerBear
import DASHI.Cognition.EpsteinWexnerTrustInstrumentAuthority20261015Exact as WexnerAuthority
import DASHI.Cognition.EpsteinFinancialTrustBearCrisisAwarenessSettlement20261014Exact as Bear
import DASHI.Cognition.EpsteinRothschildSouthernTrustServiceReceiptRound20261014Exact as Rothschild
import DASHI.Cognition.PrivateCapitalHousingAIInfrastructureCrossPollinationExact as ModernCapital

------------------------------------------------------------------------
-- FINANCIAL / SYSTEMIC PARETO — ROUND 3, 2026-10-15
--
-- Round 3 demotes already-paid existence questions and promotes exact
-- governance/economic-incidence residuals. The principal new result is that
-- the Wexner lane is not merely client proximity: primary trust instruments
-- pay Epstein trustee authority, while litigation records attribute specific
-- Bear investments to that trustee capacity. Those source classes remain
-- distinct until neutral transaction records pay the trades themselves.
------------------------------------------------------------------------

data FinanceLane3 : Set where
  wexnerTrustAuthorityAndCapitalIncidence : FinanceLane3
  valarRealisedEconomicsAndSpecialRights : FinanceLane3
  blackWorkProductImplementationAndPayment : FinanceLane3
  bearStructuredCreditLossRecovery : FinanceLane3
  southernTrustFungibleCapitalDeployment : FinanceLane3
  financialTrustFeeAndCapitalArchitecture : FinanceLane3
  couqWexnerFoundationCapitalLifecycle : FinanceLane3
  familyInterestPartnershipEconomics : FinanceLane3
  rothschildAdviceCapitalAlgorithms : FinanceLane3
  privateCapitalHousingAIInfrastructure : FinanceLane3

record FinanceProfile3 : Set where
  constructor finance-profile3
  field
    lane : FinanceLane3
    priority : Nat
    directReceiptsHigh : Bool
    governanceOrControlResidualHigh : Bool
    realisedEconomicIncidenceDebtHigh : Bool
    secondThirdOrderLeverageHigh : Bool
    reading : String
open FinanceProfile3 public

canonicalFinanceFront3 : List FinanceProfile3
canonicalFinanceFront3 =
  finance-profile3 wexnerTrustAuthorityAndCapitalIncidence 100 true true true true
    "Primary JPM-produced 1998 Wexner Children's Trust II instrument pays Wexner grantor/Epstein trustee identity, discretionary trustee authority and initial 2.5m Limited shares. Bear respondents separately attribute USD20m ABS and USD10m Europe Long/Short investments to Epstein acting in trustee capacity, while discovery requests identify trustee investments as a concrete production subject. The live cut is neutral transaction receipts, amendments/removal, complete asset ledger and beneficiary incidence; trustee authority is not beneficial ownership or proof of grantor direction." ∷
  finance-profile3 valarRealisedEconomicsAndSpecialRights 100 true true true true
    "Thiel's direct 2014 solicitation -> Southern Trust Fund II/III LP commitments -> paid capital -> 2018 partner-capital appreciation -> 2018/19 later-fund re-solicitation -> 2026 estate valuation is now a paid lifecycle. The frontier is realised distributions/net returns, side letters/co-investment rights, final estate disposition and terminal Fund IV/V participation; carrying value is not realised cash." ∷
  finance-profile3 blackWorkProductImplementationAndPayment 100 true true true true
    "Black Family Partners directly transmitted estate-planning/restructuring work product to Epstein in 2014, and a 2017 Sullivan & Cromwell Black estate-planning memorandum was forwarded to him for issue-spotting. Apollo/trust operational interfaces and the large Black payment stream are paid separately. The max-cut is executed implementation plus invoice/payment-to-work-object joining, not an Apollo-corporate-retention inference." ∷
  finance-profile3 bearStructuredCreditLossRecovery 100 true true true true
    "FTC/COUQ Bear structured-credit contributions, Enhanced rollover, partial Bear share sale and USD9.2m collective settlement are paid. Respondent records also expose other profitable Bear hedge-fund positions. The high-value residual is fund-by-fund realised loss/recovery and settlement allocation, with pleading assertions kept distinct from adjudicated merits." ∷
  finance-profile3 southernTrustFungibleCapitalDeployment 100 true false true true
    "Black/Rothschild and other inflows contribute to Southern Trust's fungible capital capacity; Valar/Honeycomb/other deployments are independently paid. Earmarked-dollar tracing is unnecessary for pool-level incidence. The remaining cut is aggregate capitalization/liquidity, return/distribution history and governance rights rather than source-specific tracing." ∷
  finance-profile3 financialTrustFeeAndCapitalArchitecture 100 true true true true
    "FTC's primary annual accounting spine and multiple payer/capital surfaces are paid. Remaining value lies in named-payer allocation, partnership/trust economics, transaction authority and realised beneficiary incidence rather than another broad entity sweep." ∷
  finance-profile3 couqWexnerFoundationCapitalLifecycle 99 true true true true
    "C.O.U.Q. received at least two source-paid Wexner-vehicle contribution surfaces totaling about USD21.205m nominal market/cash value, later invested USD10m in Bear ABS and assigned its ABS interest to YLK. Epstein is paid as a formal C.O.U.Q. officer/director. Contributions expand a fungible foundation pool; they do not prove earmarking, donor control or officer beneficial ownership."
  ∷ finance-profile3 familyInterestPartnershipEconomics 99 true true true true
    "FTC as Family Interest LP general partner, a Wexner children's trust as limited partner and the USD55.878m partnership capital movement are paid; a separate Wexner Trust II note was repaid through an FTC-funded Indyke loan. Governing agreements, exact trust identity, capital accounts and GP economics remain the useful cut."
  ∷ finance-profile3 rothschildAdviceCapitalAlgorithms 99 true true true true
    "Rothschild-Southern Trust consulting/payment and capital inflow surfaces remain source-paid. The live question is delivered work product, agreement-version/payment settlement and institutional decision consequences, not relationship existence."
  ∷ finance-profile3 privateCapitalHousingAIInfrastructure 98 true true true true
    "Modern housing/AI/power assetisation remains a strong structural consumer of the historical finance machinery. Same-manager recurrence across asset classes is paid in current transactions; same fund, common political command or historical Epstein causation are not."
  ∷ []

record Round3Boundary : Set where
  constructor round3-boundary
  field
    trusteeAuthorityIsBeneficialOwnership : Bool
    trusteeAuthorityProvesEveryTrade : Bool
    revocableTrustMeansGrantorDirectedEveryTrade : Bool
    contributionToFungiblePoolRequiresEarmarking : Bool
    directWorkTransmissionMeansAuthorship : Bool
    carryingValueMeansRealisedCash : Bool
    laterFundSolicitationMeansInvestment : Bool
    settlementMeansAdmission : Bool
    historicalFinanceRelationshipImpliesModernStrategy : Bool
    sourceTypedGovernanceAndIncidenceWorthInvestigating : Bool
open Round3Boundary public

canonicalRound3Boundary : Round3Boundary
canonicalRound3Boundary = round3-boundary
  false false false false false false false false false true

data TrusteeAuthorityImpliesBeneficialOwnership : Set where
data FormalAuthorityImpliesSpecificTrade : Set where
data RevocableTrustImpliesTradeDirection : Set where
data FungiblePoolImpliesEarmarking : Set where
data TransmissionImpliesAuthorship : Set where
data ValuationImpliesRealisedCash : Set where
data SolicitationImpliesInvestment : Set where

trusteeAuthorityDoesNotCreateBeneficialOwnership : TrusteeAuthorityImpliesBeneficialOwnership → ⊥
trusteeAuthorityDoesNotCreateBeneficialOwnership ()

formalAuthorityDoesNotCreateSpecificTrade : FormalAuthorityImpliesSpecificTrade → ⊥
formalAuthorityDoesNotCreateSpecificTrade ()

revocableTrustDoesNotCreateTradeDirection : RevocableTrustImpliesTradeDirection → ⊥
revocableTrustDoesNotCreateTradeDirection ()

fungiblePoolDoesNotRequireEarmarking : FungiblePoolImpliesEarmarking → ⊥
fungiblePoolDoesNotRequireEarmarking ()

transmissionDoesNotCreateAuthorship : TransmissionImpliesAuthorship → ⊥
transmissionDoesNotCreateAuthorship ()

valuationDoesNotCreateRealisedCash : ValuationImpliesRealisedCash → ⊥
valuationDoesNotCreateRealisedCash ()

solicitationDoesNotCreateInvestment : SolicitationImpliesInvestment → ⊥
solicitationDoesNotCreateInvestment ()

------------------------------------------------------------------------
-- Current max-cut after Round 3.
------------------------------------------------------------------------

data Round3Debt : Set where
  wexnerTrustNeutralBearTransactions : Round3Debt
  wexnerTrustAmendmentRemovalAssetLedger : Round3Debt
  valarDistributionsSideLettersEstateExit : Round3Debt
  blackImplementationPaymentWorkJoin : Round3Debt
  bearRealisedLossRecoverySettlementAllocation : Round3Debt
  familyInterestAgreementCapitalAccounts : Round3Debt
  couqGovernanceDonorGrantLedger : Round3Debt
  rothschildDeliveredWorkProduct : Round3Debt

record Round3Acquisition : Set where
  constructor round3-acquisition
  field
    debt : Round3Debt
    priority : Nat
    likelyPublicCorpusClosable : Bool
    instruction : String
open Round3Acquisition public

canonicalRound3Acquisition : List Round3Acquisition
canonicalRound3Acquisition =
  round3-acquisition wexnerTrustNeutralBearTransactions 100 true
    "Acquire executed ABS and Europe Long/Short subscriptions/wires/capital-account records naming Wexner Children's Trust II; use them to promote or correct the Bear respondents' USD20m/USD10m assertions." ∷
  round3-acquisition wexnerTrustAmendmentRemovalAssetLedger 100 true
    "Acquire trust amendments/successor-trustee records and the complete trust asset/contribution/distribution ledger to resolve the duration and incidence of Epstein's formal authority." ∷
  round3-acquisition valarDistributionsSideLettersEstateExit 100 true
    "Acquire realised Valar distributions/net returns, Southern Trust-specific side letters/co-investment rights and the final 2026 estate disposition; do not substitute manager carrying values for cash returns." ∷
  round3-acquisition blackImplementationPaymentWorkJoin 100 true
    "Join transmitted Black work products to executed trust/tax transactions and dated invoices/payment tranches; transmission/review is already paid but authorship and implementation remain separate." ∷
  round3-acquisition bearRealisedLossRecoverySettlementAllocation 100 true
    "Reconstruct Bear fund-by-fund realised economics and allocate the USD9.2m settlement before estimating net loss/recovery or joining crisis losses to annual FTC accounting." ∷
  round3-acquisition familyInterestAgreementCapitalAccounts 99 true
    "Acquire Family Interest LP governing agreement and capital accounts plus exact identity of its Wexner-family trust limited partner; GP authority is not beneficial ownership." ∷
  round3-acquisition couqGovernanceDonorGrantLedger 99 true
    "Acquire C.O.U.Q. governing authority, full donor ledger, grant/distribution ledger and YLK instrument to measure foundation capital incidence without earmarking assumptions." ∷
  round3-acquisition rothschildDeliveredWorkProduct 98 true
    "Join Rothschild agreements/invoices/wires to delivered algorithm/risk/estate work product and downstream implementation authority." ∷
  []
