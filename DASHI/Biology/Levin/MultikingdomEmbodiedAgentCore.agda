module DASHI.Biology.Levin.MultikingdomEmbodiedAgentCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ElectrochemicalBodyConsortium as Consortium
import DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary as Appetite
import DASHI.Biology.Levin.CravingCausalCompetition as Craving
import DASHI.Biology.Levin.EndosymbioticOrganelleAgencyBoundary as Organelle
import DASHI.Biology.Levin.FungalNetworkAgencyBoundary as Fungal
import DASHI.Biology.Levin.ComponentCausalRoleBoundary as CausalRole
import DASHI.Biology.Levin.HostMicrobeCellCountBoundary as CellCount
import DASHI.Biology.Levin.PolycomputationBiologyAdapter as Poly
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy

record SiphonophoreAnalogyBoundary : Set where
  field
    multipleSemiAutonomousComponents : Bool
    divisionOfLabourAcrossComponents : Bool
    collectiveBoundaryMaintained : Bool
    reproductiveBottleneckDiffers : Bool
    developmentalIntegrationDiffers : Bool
    analogyNotTaxonomicIdentity : Bool
    analogyNotProofOfEqualComponentAgency : Bool

canonicalSiphonophoreAnalogyBoundary : SiphonophoreAnalogyBoundary
canonicalSiphonophoreAnalogyBoundary = record
  { multipleSemiAutonomousComponents = true
  ; divisionOfLabourAcrossComponents = true
  ; collectiveBoundaryMaintained = true
  ; reproductiveBottleneckDiffers = true
  ; developmentalIntegrationDiffers = true
  ; analogyNotTaxonomicIdentity = true
  ; analogyNotProofOfEqualComponentAgency = true
  }

record MultikingdomEmbodiedAgentCore : Set where
  field
    consortiumBoundary : Consortium.ElectrochemicalBodyConsortiumBoundary
    appetiteBoundary : Appetite.MicrobiomeHostAppetiteBoundary
    cravingBoundary : Craving.CravingCausalCompetitionBoundary
    organelleBoundary : Organelle.EndosymbioticOrganelleAgencyBoundary
    fungalBoundary : Fungal.FungalNetworkAgencyBoundary
    causalRoleBoundary : CausalRole.ComponentCausalRoleBoundary
    cellCountBoundary : CellCount.HostMicrobeCellCountBoundary
    siphonophoreAnalogyBoundary : SiphonophoreAnalogyBoundary
    polycomputationAdapter : Poly.PolycomputationBiologyAdapter
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    organismIsNestedCoalition : Bool
    coalitionDoesNotEraseHigherLevelIndividual : Bool
    componentInfluenceNotComponentControl : Bool
    goalsMayAlignConflictOrRemainOrthogonal : Bool
    causalClaimsRequireIntervention : Bool
    ethicalStatusNotDerivedFromCellCounts : Bool
    interpretation : String

canonicalMultikingdomEmbodiedAgentCore : MultikingdomEmbodiedAgentCore
canonicalMultikingdomEmbodiedAgentCore = record
  { consortiumBoundary = Consortium.canonicalElectrochemicalBodyConsortiumBoundary
  ; appetiteBoundary = Appetite.canonicalMicrobiomeHostAppetiteBoundary
  ; cravingBoundary = Craving.canonicalCravingCausalCompetitionBoundary
  ; organelleBoundary = Organelle.canonicalEndosymbioticOrganelleAgencyBoundary
  ; fungalBoundary = Fungal.canonicalFungalNetworkAgencyBoundary
  ; causalRoleBoundary = CausalRole.canonicalComponentCausalRoleBoundary
  ; cellCountBoundary = CellCount.canonicalHostMicrobeCellCountBoundary
  ; siphonophoreAnalogyBoundary = canonicalSiphonophoreAnalogyBoundary
  ; polycomputationAdapter = Poly.canonicalPolycomputationBiologyAdapter
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; organismIsNestedCoalition = true
  ; coalitionDoesNotEraseHigherLevelIndividual = true
  ; componentInfluenceNotComponentControl = true
  ; goalsMayAlignConflictOrRemainOrthogonal = true
  ; causalClaimsRequireIntervention = true
  ; ethicalStatusNotDerivedFromCellCounts = true
  ; interpretation = "A human-scale agent is a dynamically maintained coalition spanning host cells, organelles, organs, microbiota and signalling environments; lower-level systems may bias higher-level behaviour, but no layer is granted exclusive authorship without causal and scale-specific evidence"
  }
