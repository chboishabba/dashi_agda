module DASHI.Law.SensibLawSpringfieldFirstNineApprovalGasEndpointBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Influence

------------------------------------------------------------------------
-- The 2018 First Nine approval is used here only as an exact Commonwealth
-- identity / action / land-development coordinate.  It does not mention gas
-- and cannot pay a gas-infrastructure or lobbying proposition.
------------------------------------------------------------------------

firstNineFinalApproval : Source.AttributedSource
firstNineFinalApproval = Source.mkNoDOISource
  "Australian Government Department of the Environment and Energy"
  "Approval — First Nine master planned residential development, Brookwater, Qld (2016/7676)"
  "EPBC approval decision"
  "2018"
  "EPBC 2016/7676 approval decision notice"
  Source.governmentSource
  "Primary Commonwealth approval identifying Springfield Land Corporation Pty Limited as approval holder and imposing a maximum 46.2 ha koala-habitat clearing limit plus offset and monitoring conditions. This source contains no proposition about household gas, gas-network ownership or lobbying."
  Source.publicAttribution

record ApprovalIdentityBridge : Set where
  constructor approval-identity-bridge
  field
    projectRef : String
    approvalHolderACN : String
    sameSpringfieldEntityCoordinate : Bool
    sourceMentionsGas : Bool
    sourceMentionsLobbying : Bool
    importsGasConclusion : Bool
    importsGasConclusionIsFalse : importsGasConclusion ≡ false

firstNineSpringfieldIdentityBridge : ApprovalIdentityBridge
firstNineSpringfieldIdentityBridge = approval-identity-bridge
  "EPBC 2016/7676"
  "055 714 531"
  true
  false
  false
  false refl

data EnvironmentalApprovalPaysGasIntent : Set where
data OffsetConditionPaysEnergyOwnership : Set where

environmentalApprovalDoesNotPayGasIntent : EnvironmentalApprovalPaysGasIntent → ⊥
environmentalApprovalDoesNotPayGasIntent ()

offsetConditionDoesNotPayEnergyOwnership : OffsetConditionPaysEnergyOwnership → ⊥
offsetConditionDoesNotPayEnergyOwnership ()

record BridgeUsePolicy : Set where
  constructor bridge-use-policy
  field
    useApprovalForIdentity : Bool
    useApprovalForProjectGeometry : Bool
    useApprovalForGasSpecification : Bool
    useApprovalForLobbyingCausation : Bool

canonicalBridgeUsePolicy : BridgeUsePolicy
canonicalBridgeUsePolicy = bridge-use-policy true true false false
