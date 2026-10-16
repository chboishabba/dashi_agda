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
  4 0 4 false false
  "Current observations support rising usage/spend, falling average unit price, rising open-weight production share, and continued physical/demand growth. They do not yet pay a global same-capability scarcity-rent trajectory, realised capital-return trajectory, or refinancing outcome."

refinancingStressFit : OutcomeFit
refinancingStressFit = outcome-fit
  "refinancing stress"
  6 0 2 false false
  "Current observations support strong demand alongside negative CoreWeave capital-spread bounds, sharply worse CoreWeave credit pricing, rising financing pressure, high open-weight substitution and falling unit price. Actual default/refinancing failure and a broad persistent regime remain unpaid."

durableRentFit : OutcomeFit
durableRentFit = outcome-fit
  "durable-rent expansion"
  2 2 4 false false
  "Demand/buildout supply supportive coordinates, while falling gateway unit prices and CoreWeave negative capital-return/credit-stress coordinates are contrary for the selected observations. Layer-specific positive landlord economics prevent global rejection."

orderlyCapitalRotationFit : OutcomeFit
orderlyCapitalRotationFit = outcome-fit
  "orderly capital rotation"
  4 1 3 false false
  "Open-weight share, falling unit prices, rising usage and positive landlord/project economics are compatible with capital rotation, while the selected CoreWeave tenant credit/capital-return stress is a contrary coordinate. Broader realised returns and refinancing remain open."

policyMoatFit : OutcomeFit
policyMoatFit = outcome-fit
  "policy/compliance moat"
  0 1 7 false false
  "Australia currently supplies a negative/control observation because the earlier general mandatory-guardrail proposal is not proceeding. No realised mandatory actor-class cost or concentration response is paid."

anyTerminalRegimeSelected : Bool
anyTerminalRegimeSelected = false

selectedObservationsSupportTwoLeadingRivals :
  (supportedCoordinates commoditisationFit ≡ 4) ×
  (supportedCoordinates refinancingStressFit ≡ 6)
selectedObservationsSupportTwoLeadingRivals = refl , refl

terminalPromotionStillClosed : anyTerminalRegimeSelected ≡ false
terminalPromotionStillClosed = refl

data PartialFitSelectsRegimePermission : Set where
data OneIssuerStressSelectsSystemRegimePermission : Set where
data NegativePolicyControlRefutesFutureMoatPermission : Set where

partialFitDoesNotSelectRegime : PartialFitSelectsRegimePermission → ⊥
partialFitDoesNotSelectRegime ()

oneIssuerStressDoesNotSelectSystemRegime : OneIssuerStressSelectsSystemRegimePermission → ⊥
oneIssuerStressDoesNotSelectSystemRegime ()

negativePolicyControlDoesNotRefuteFutureMoat : NegativePolicyControlRefutesFutureMoatPermission → ⊥
negativePolicyControlDoesNotRefuteFutureMoat ()

boundary : String
boundary =
  "The predeclared outcome signatures are now evaluated against the October-2026 evidence without post-hoc redefining them. The strongest selected-coordinate compatibility is with refinancing stress and commoditisation-with-volume-growth; orderly capital rotation remains materially compatible because some infrastructure/landlord layers retain positive economics, while durable-rent expansion has contrary selected unit-price/capital-return coordinates. Australia's guardrail retreat is contrary to a present general policy-moat instantiation. No terminal regime is selected: full signatures require broader same-basis longitudinal returns, refinancing/default outcomes, scarcity-rent trajectories and market-structure evidence."
