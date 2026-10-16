module DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICapitalOutcomeSignatures20261016Exact as Signature
import DASHI.Economics.AICapitalSOTAReconciliation20261016Exact as SOTA
import DASHI.Economics.AICoreWeaveCreditDeterioration20261016Exact as Credit
import DASHI.Economics.AICapitalPhase2Acquisition20261016Exact as Acquisition
import DASHI.Economics.AIOpenWeightProviderIntermediation20261016Exact as Intermediation
import DASHI.Economics.AIFrontierAdjustedProfitabilityCounterweight20261016Exact as Frontier

record OutcomeFit : Set where
  constructor outcome-fit
  field
    signatureName : String
    supportedCoordinates : Nat
    contraryCoordinates : Nat
    unresolvedCoordinates : Nat
    fullSignaturePaid : Bool
    terminalSelectionAllowed : Bool
    interpretation : String

open OutcomeFit public

commoditisationFit : OutcomeFit
commoditisationFit = outcome-fit
  "commoditisation with volume growth"
  5 0 3 false false
  "Current observations support rising usage/spend, falling average unit price, rising open-weight production share, continued physical/demand growth, and rapid growth of open-weight spend. They do not yet pay a global same-capability scarcity-rent trajectory, realised cross-sector capital-return trajectory, or broad refinancing outcome. Provider intermediation prevents open-weight adoption from being identified with disintermediation."

refinancingStressFit : OutcomeFit
refinancingStressFit = outcome-fit
  "refinancing stress"
  6 0 2 false false
  "Current observations support strong demand alongside negative CoreWeave capital-spread bounds, sharply worse CoreWeave credit pricing, rising financing pressure, high open-weight substitution and falling unit price. Actual default/refinancing failure and a broad persistent regime remain unpaid."

durableRentFit : OutcomeFit
durableRentFit = outcome-fit
  "durable-rent expansion"
  3 2 3 false false
  "Demand/buildout and Anthropic's reported adjusted Q3 profitability supply supportive coordinates, while falling gateway unit prices and CoreWeave negative capital-return/credit-stress coordinates are contrary for the selected observations. Adjusted private-company profitability is not GAAP/FCF/ROIC, and layer-specific positive landlord economics prevent global rejection."

orderlyCapitalRotationFit : OutcomeFit
orderlyCapitalRotationFit = outcome-fit
  "orderly capital rotation"
  6 1 2 false false
  "Open-weight share, falling unit prices, rising usage, positive landlord/project economics, simultaneous open/closed spend growth and US-provider intermediation of Chinese-origin models are compatible with value rotation across model, hosting and application layers. CoreWeave tenant credit/capital-return stress is a contrary coordinate. Broader realised returns and refinancing remain open."

policyMoatFit : OutcomeFit
policyMoatFit = outcome-fit
  "policy/compliance moat"
  0 1 7 false false
  "Australia currently supplies a negative/control observation for a general model/deployment moat because the earlier mandatory-guardrail proposal is not proceeding. Infrastructure-focused data-centre expectations and announced future duties are a distinct hypothesis and do not yet supply realised actor-class cost or concentration effects."

anyTerminalRegimeSelected : Bool
anyTerminalRegimeSelected = false

selectedObservationsSupportTwoLeadingRivals :
  (supportedCoordinates commoditisationFit ≡ 5) ×
  (supportedCoordinates refinancingStressFit ≡ 6)
selectedObservationsSupportTwoLeadingRivals = refl , refl

orderlyRotationNowCoLeadingOnSelectedCoordinates : supportedCoordinates orderlyCapitalRotationFit ≡ 6
orderlyRotationNowCoLeadingOnSelectedCoordinates = refl

frontierCounterweightPaid : Frontier.adjustedProfitabilityReported Frontier.anthropicQ3Counterweight ≡ true
frontierCounterweightPaid = Frontier.adjustedProfitabilityReportedPaid

providerIntermediationCounterweightPaid : Intermediation.usProviderChineseModelIntermediationPaid Intermediation.vercelProviderIntermediation ≡ true
providerIntermediationCounterweightPaid = Intermediation.usProviderIntermediationPaid

terminalPromotionStillClosed : anyTerminalRegimeSelected ≡ false
terminalPromotionStillClosed = refl

data PartialFitSelectsRegimePermission : Set where
data OneIssuerStressSelectsSystemRegimePermission : Set where
data NegativePolicyControlRefutesFutureMoatPermission : Set where

data AdjustedFrontierProfitSelectsDurableRentPermission : Set where

partialFitDoesNotSelectRegime : PartialFitSelectsRegimePermission → ⊥
partialFitDoesNotSelectRegime ()

oneIssuerStressDoesNotSelectSystemRegime : OneIssuerStressSelectsSystemRegimePermission → ⊥
oneIssuerStressDoesNotSelectSystemRegime ()

negativePolicyControlDoesNotRefuteFutureMoat : NegativePolicyControlRefutesFutureMoatPermission → ⊥
negativePolicyControlDoesNotRefuteFutureMoat ()

adjustedFrontierProfitDoesNotSelectDurableRent : AdjustedFrontierProfitSelectsDurableRentPermission → ⊥
adjustedFrontierProfitDoesNotSelectDurableRent ()

boundary : String
boundary =
  "The predeclared outcome signatures are evaluated against October-2026 evidence without post-hoc redefining them. Refinancing stress remains strongly compatible; commoditisation-with-volume-growth remains strongly compatible; and orderly capital rotation is now equally strong on the selected-coordinate count because open-weight expansion coexists with simultaneous closed-model spend growth and substantial provider intermediation, while Anthropic's reported adjusted profitability supplies a bounded frontier counterweight. Durable-rent expansion is therefore not globally rejected, but adjusted private-company profitability is not audited GAAP profit, FCF or ROIC. Australia's guardrail retreat is contrary to a present general model-compliance moat, while infrastructure-focused regulation remains a separate unmeasured hypothesis. No terminal regime is selected."
