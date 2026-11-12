module DASHI.Governance.CybersynCrossSectorScenarioExact where

-- DASHI original finite scenario kernel, NOT a forecast.
-- Exogenous shocks, policy choices, balance-sheet transfers, and political
-- narratives are separate coordinates. Every real-world coefficient remains
-- an externally calibrated and provenance-bound obligation.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Cyber
import DASHI.Governance.CybersynPhysicalFinanceCutExact as Accounting
import DASHI.Governance.CybersynAuthorityFeedbackExact as Authority
import DASHI.Economics.SystemicCrisisCompressionBridge as Crisis
import DASHI.Economics.GeopoliticalEnergyAITreasuryTransmissionExact as Geo
import DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact as Yen

infixr 6 _and_
_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

infixr 5 _or_
_or_ : Bool → Bool → Bool
true or _ = true
false or b = b

data PolicyChoice : Set where
  publicGuarantee : PolicyChoice
  firmRiskRetained : PolicyChoice
  conditionalCommunityProvisioning : PolicyChoice

data Shock : Set where
  energyDisruption : Shock
  fertiliserFoodDisruption : Shock
  climateHazard : Shock
  yenFundingReversal : Shock
  aiCollateralRepricing : Shock
  housingCreditDistress : Shock
  supplyChainFailure : Shock

record Exposures : Set where
  constructor exposures
  field
    energy : Bool
    food : Bool
    climate : Bool
    fxFunding : Bool
    aiCredit : Bool
    housing : Bool
    infrastructure : Bool
open Exposures public

noStress : Exposures
noStress = exposures false false false false false false false

applyShock : Shock → Exposures → Exposures
applyShock energyDisruption x =
  exposures true (food x) (climate x) (fxFunding x)
    (aiCredit x) (housing x) (infrastructure x)
applyShock fertiliserFoodDisruption x =
  exposures (energy x) true (climate x) (fxFunding x)
    (aiCredit x) (housing x) (infrastructure x)
applyShock climateHazard x =
  exposures (energy x) (food x) true (fxFunding x)
    (aiCredit x) (housing x) (infrastructure x)
applyShock yenFundingReversal x =
  exposures (energy x) (food x) (climate x) true
    (aiCredit x) (housing x) (infrastructure x)
applyShock aiCollateralRepricing x =
  exposures (energy x) (food x) (climate x) (fxFunding x)
    true (housing x) (infrastructure x)
applyShock housingCreditDistress x =
  exposures (energy x) (food x) (climate x) (fxFunding x)
    (aiCredit x) true (infrastructure x)
applyShock supplyChainFailure x =
  exposures (energy x) (food x) (climate x) (fxFunding x)
    (aiCredit x) (housing x) true

-- A transparent nonlinear interaction rule, chosen only as a synthetic
-- counterexample to additive/single-factor crisis inference.
coupledCascade : Exposures → Bool
coupledCascade x =
  (energy x and food x) or
  (fxFunding x and aiCredit x) or
  (climate x and infrastructure x) or
  (housing x and fxFunding x)

energyAloneDoesNotTrigger :
  coupledCascade (applyShock energyDisruption noStress) ≡ false
energyAloneDoesNotTrigger = refl

foodAloneDoesNotTrigger :
  coupledCascade (applyShock fertiliserFoodDisruption noStress) ≡ false
foodAloneDoesNotTrigger = refl

twoShocksTrigger :
  coupledCascade
    (applyShock fertiliserFoodDisruption
      (applyShock energyDisruption noStress)) ≡ true
twoShocksTrigger = refl

yenAndCollateralTrigger :
  coupledCascade
    (applyShock aiCollateralRepricing
      (applyShock yenFundingReversal noStress)) ≡ true
yenAndCollateralTrigger = refl

-- Government subsidy is not private profit and public exposure is not
-- erased by counting the capital project as successful.
record PublicRiskTransfer : Set where
  constructor publicRiskTransfer
  field
    privateUpsideRetained : Bool
    publicDownsideGuaranteed : Bool
    taxpayerLiabilityVisible : Bool
    regulatoryCostRecovery : Bool
open PublicRiskTransfer public

unpricedGuarantee : PublicRiskTransfer
unpricedGuarantee = publicRiskTransfer true true false false

fullyDisclosedGuarantee : PublicRiskTransfer
fullyDisclosedGuarantee = publicRiskTransfer true true true true

-- Visibility is required even when risk transfer is permitted.
riskTransferTransparent : PublicRiskTransfer → Bool
riskTransferTransparent r =
  taxpayerLiabilityVisible r and regulatoryCostRecovery r

undisclosedRiskFailsTransparency :
  riskTransferTransparent unpricedGuarantee ≡ false
undisclosedRiskFailsTransparency = refl

disclosedRiskPassesThisNarrowGate :
  riskTransferTransparent fullyDisclosedGuarantee ≡ true
disclosedRiskPassesThisNarrowGate = refl

-- The narrow gate is not an assertion that a disclosed guarantee is socially
-- desirable, democratically authorised or commercially sound.
record StrategicAgentConstraints : Set where
  constructor strategicAgentConstraints
  field
    fiscalHeadroom : Bool
    electionPressure : Bool
    infrastructureBottleneck : Bool
    insurerCapitalAdequacy : Bool
    bankFundingLiquidity : Bool
    householdBasicNeeds : Bool
    communityAuthorised : Bool
open StrategicAgentConstraints public

admissiblePublicGuarantee : StrategicAgentConstraints → Bool
admissiblePublicGuarantee a =
  fiscalHeadroom a and insurerCapitalAdequacy a and
  bankFundingLiquidity a and householdBasicNeeds a and
  communityAuthorised a

-- Political incentive can be intense without satisfying the actual
-- authorisation, financing and social viability conditions.
stressedElection : StrategicAgentConstraints
stressedElection =
  strategicAgentConstraints false true true false false false false

pressureIsNotPublicGuaranteeAdmission :
  admissiblePublicGuarantee stressedElection ≡ false
pressureIsNotPublicGuaranteeAdmission = refl

-- Policy is separate from balance-sheet conditions; changing the label on
-- an action does not itself change physical or economic outcomes.
policyHeadline : PolicyChoice → Bool
policyHeadline _ = true

data LossBearer : Set where
  householdTaxpayer : LossBearer
  privateShareholder : LossBearer
  lenderCapital : LossBearer

whoBearsFirstLoss : PolicyChoice → LossBearer
whoBearsFirstLoss publicGuarantee = householdTaxpayer
whoBearsFirstLoss firmRiskRetained = privateShareholder
whoBearsFirstLoss conditionalCommunityProvisioning = lenderCapital

sameInvestmentAnnouncement :
  policyHeadline publicGuarantee ≡
  policyHeadline firmRiskRetained
sameInvestmentAnnouncement = refl

differentLossAllocation :
  whoBearsFirstLoss publicGuarantee ≡
  whoBearsFirstLoss firmRiskRetained → ⊥
differentLossAllocation ()

-- Existing owners are consumed as separate interpretations, never promoted
-- from the illustrative Boolean interaction into empirical evidence.
crisisTransmissionOwner : Crisis.TransmissionChain
crisisTransmissionOwner = Crisis.triggerOnlyChain
  (Yen.leveragedCarryUnwind (Yen.yenFundingValve
    Yen.zer Yen.zer Yen.zer Yen.zer Yen.zer Yen.zer Yen.zer))

hormuzTransmissionOwner : Geo.GeopoliticalNode
hormuzTransmissionOwner = Geo.hormuz

-- No claim of general crash inevitability or real crisis timing.
data IllustrativeCascadeImpliesObservedCrisis : Set where
illustrativeDoesNotCertifyObservedCrisis :
  IllustrativeCascadeImpliesObservedCrisis → ⊥
illustrativeDoesNotCertifyObservedCrisis ()
