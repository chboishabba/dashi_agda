module DASHI.Economics.AICapitalOutcomeSignatures20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

data Direction : Set where
  rising falling positive negative flat unknown : Direction

record OutcomeSignature : Set where
  constructor outcome-signature
  field
    name : String
    demandDirection : Direction
    unitPriceDirection : Direction
    scarcityRentDirection : Direction
    capitalReturnDirection : Direction
    fundingPressureDirection : Direction
    utilisationDirection : Direction
    openWeightShareDirection : Direction
    refinancingOutcome : Direction
    interpretation : String

open OutcomeSignature public

durableRentExpansion : OutcomeSignature
durableRentExpansion = outcome-signature
  "durable-rent expansion"
  rising flat flat positive flat rising flat positive
  "AI demand and utilisation rise while unit economics remain sufficiently durable for realised returns and refinancing to stay healthy."

commoditisationWithVolumeGrowth : OutcomeSignature
commoditisationWithVolumeGrowth = outcome-signature
  "commoditisation with volume growth"
  rising falling falling unknown flat rising rising unknown
  "Task/token volume and AI spend grow while average unit price and model scarcity rents fall; infrastructure may remain heavily used even as value migrates away from model scarcity."

refinancingStress : OutcomeSignature
refinancingStress = outcome-signature
  "refinancing stress"
  rising falling falling negative rising unknown rising negative
  "Demand can remain strong while capital returns deteriorate, funding spreads rise and rollover/refinancing outcomes worsen."

orderlyCapitalRotation : OutcomeSignature
orderlyCapitalRotation = outcome-signature
  "orderly capital rotation"
  rising falling falling positive flat rising rising positive
  "Model scarcity compresses, but lower costs, utilisation and layer-specific economics allow capital to rotate toward infrastructure/providers or applications without broad distress."

policyMoat : OutcomeSignature
policyMoat = outcome-signature
  "policy/compliance moat"
  unknown unknown unknown positive flat unknown falling positive
  "Operative compliance obligations impose persistently higher proportional costs on entrants/open-weight suppliers than incumbents and are followed by concentration or exit responses after admissible causal identification."

currentOutcomePromotionReady : Bool
currentOutcomePromotionReady = false

data SnapshotSelectsOutcomePermission : Set where
data OneMetricSelectsOutcomePermission : Set where
data PolicyProposalSelectsMoatPermission : Set where

snapshotDoesNotSelectOutcome : SnapshotSelectsOutcomePermission → ⊥
snapshotDoesNotSelectOutcome ()

oneMetricDoesNotSelectOutcome : OneMetricSelectsOutcomePermission → ⊥
oneMetricDoesNotSelectOutcome ()

policyProposalDoesNotSelectMoat : PolicyProposalSelectsMoatPermission → ⊥
policyProposalDoesNotSelectMoat ()

boundary : String
boundary =
  "Five rival outcome signatures are predeclared before the next longitudinal observations: durable-rent expansion; commoditisation with volume growth; refinancing stress; orderly capital rotation; and a policy/compliance moat. Current October-2026 observations are deliberately not promoted to any one terminal outcome because the signatures require multiple same-basis longitudinal coordinates. Snapshot stress, one metric, or a policy proposal cannot select a regime by itself."
