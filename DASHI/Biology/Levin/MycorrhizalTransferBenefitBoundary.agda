module DASHI.Biology.Levin.MycorrhizalTransferBenefitBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ComponentCausalRoleBoundary as Causal
import DASHI.Biology.Levin.MycelialTransportTopology as Topology
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy

record MycorrhizalTransferProtocol : Set where
  field
    donorSpecified : Bool
    receiverSpecified : Bool
    fungalConnectionVerified : Bool
    transferredMaterialIdentified : Bool
    alternativeSoilRouteExcluded : Bool
    transferDirectionMeasured : Bool
    energeticCostMeasured : Bool
    donorFitnessEffectMeasured : Bool
    receiverFitnessEffectMeasured : Bool
    kinshipHypothesisSpecified : Bool
    networkDisruptionControlIncluded : Bool

record MycorrhizalTransferBenefitBoundary : Set where
  field
    causalRoleBoundary : Causal.ComponentCausalRoleBoundary
    topologyBoundary : Topology.MycelialTransportTopologyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    connectionNotTransfer : Bool
    transferNotNetBenefit : Bool
    netBenefitNotDirectedAid : Bool
    directedAidNotKinPreference : Bool
    ecosystemEffectNotForestWideIntent : Bool
    speciesAndContextSpecificityRequired : Bool
    managementAuthorityRequiresSeparateEvidence : Bool
    interpretation : String

canonicalMycorrhizalTransferBenefitBoundary : MycorrhizalTransferBenefitBoundary
canonicalMycorrhizalTransferBenefitBoundary = record
  { causalRoleBoundary = Causal.canonicalComponentCausalRoleBoundary
  ; topologyBoundary = Topology.canonicalMycelialTransportTopologyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; connectionNotTransfer = true
  ; transferNotNetBenefit = true
  ; netBenefitNotDirectedAid = true
  ; directedAidNotKinPreference = true
  ; ecosystemEffectNotForestWideIntent = true
  ; speciesAndContextSpecificityRequired = true
  ; managementAuthorityRequiresSeparateEvidence = true
  ; interpretation = "Common mycorrhizal connection, material transfer, net fitness benefit, directed aid and kin preference are separate promotion stages requiring path controls, energetic accounting and species-specific intervention evidence"
  }
