module DASHI.Cognition.EpsteinOperationalAccessNarrativeParetoRoundExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinCBPBorderAccessInvestigationExact as CBP
import DASHI.Cognition.TurningPointEpsteinNarrativePressureExact as TPUSA
import DASHI.Cognition.CharlieKirkAssassinationEvidenceSpeculationBoundaryExact as Kirk
import DASHI.Cognition.AustraliaMandelsonMiningTaxPoliticalEconomyBridgeExact as MiningTax

------------------------------------------------------------------------
-- OPERATIONAL ACCESS / NARRATIVE PRESSURE PARETO RECUT
------------------------------------------------------------------------

data RoundLane : Set where
  borderAccessCBP : RoundLane
  trumpBannonTurningPointNarrative : RoundLane
  australiaMiningTaxPoliticalEconomy : RoundLane
  kirkAssassinationSpeculationBoundary : RoundLane

record RoundProfile : Set where
  constructor round-profile
  field
    lane : RoundLane
    scalarRoutingPriority : Nat
    directPrimaryGainHigh : Bool
    systemicBridgeHigh : Bool
    secondOrderLeverageHigh : Bool
    thirdOrderLeverageHigh : Bool
    primaryResolutionDebtHigh : Bool
    speculationRiskHigh : Bool
    reading : String
open RoundProfile public

cbpProfile : RoundProfile
cbpProfile = round-profile
  borderAccessCBP 98
  true true true true true false
  "Direct operational-access seam: border inspection, officer discretion, travel logistics and federal corruption investigation. High value because it touches how Epstein physically crossed an institutional perimeter; knowledge of trafficking and agency-wide complicity remain unpaid."

tpusaProfile : RoundProfile
tpusaProfile = round-profile
  trumpBannonTurningPointNarrative 93
  true true true true true true
  "Narrative-governance seam: visible base revolt, leadership pivot, Bannon pressure and later attention attenuation. High for trust/agenda-setting dynamics but not an Epstein operational relationship."

miningTaxProfile : RoundProfile
miningTaxProfile = round-profile
  australiaMiningTaxPoliticalEconomy 87
  true true true true true false
  "Concrete transnational political-economy edge: Mandelson shared/endorsed anti-mining-tax strategy with Epstein concerning the Rudd government. Outcome causation remains unpaid."

kirkProfile : RoundProfile
kirkProfile = round-profile
  kirkAssassinationSpeculationBoundary 40
  true false false true false true
  "Evidence-boundary lane only: the physical rifle-attack layer is strongly sourced, while exploding-mic/foreign-intelligence/false-flag/patsy/inside-job claims remain speculation. Acquisition value is mainly provenance/disinformation analysis, not core Epstein-network expansion."

currentRound : List RoundProfile
currentRound = cbpProfile ∷ tpusaProfile ∷ miningTaxProfile ∷ kirkProfile ∷ []

cbpOfficerContactPaid :
  CBP.officerContactPaid CBP.canonicalBorderAccessBoundary ≡ true
cbpOfficerContactPaid = refl

cbpTraffickingKnowledgeStillUnpaid :
  CBP.traffickingKnowledgePaid CBP.canonicalBorderAccessBoundary ≡ false
cbpTraffickingKnowledgeStillUnpaid = refl

tpusaPressurePaid :
  TPUSA.tpusaBasePressurePaid TPUSA.canonicalTPUSEpsteinNarrativeBoundary ≡ true
tpusaPressurePaid = refl

tpusaDirectEpsteinRelationshipStillUnpaid :
  TPUSA.directTPUSAEpsteinRelationshipPaid TPUSA.canonicalTPUSEpsteinNarrativeBoundary ≡ false
tpusaDirectEpsteinRelationshipStillUnpaid = refl

kirkConspiracyClaimsRemainUnpaid :
  Kirk.foreignIntelligenceHitPaid Kirk.canonicalKirkEvidenceBoundary ≡ false
kirkConspiracyClaimsRemainUnpaid = refl

miningTaxBridgePaid :
  MiningTax.australianResourcePolicyBridgePaid MiningTax.canonicalMiningTaxPoliticalEconomyBoundary ≡ true
miningTaxBridgePaid = refl

data OperationalAccessImpliesTraffickingKnowledge : Set where
data NarrativePressureImpliesControlledOpposition : Set where
data PoliticalAdviceImpliesOutcomeControl : Set where
data AssassinationSpeculationImpliesHiddenActor : Set where

operationalAccessDoesNotCreateKnowledge : OperationalAccessImpliesTraffickingKnowledge → ⊥
operationalAccessDoesNotCreateKnowledge ()

narrativePressureDoesNotCreateControlledOpposition : NarrativePressureImpliesControlledOpposition → ⊥
narrativePressureDoesNotCreateControlledOpposition ()

politicalAdviceDoesNotCreateOutcomeControl : PoliticalAdviceImpliesOutcomeControl → ⊥
politicalAdviceDoesNotCreateOutcomeControl ()

assassinationSpeculationDoesNotCreateHiddenActor : AssassinationSpeculationImpliesHiddenActor → ⊥
assassinationSpeculationDoesNotCreateHiddenActor ()
