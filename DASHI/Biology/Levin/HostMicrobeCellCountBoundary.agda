module DASHI.Biology.Levin.HostMicrobeCellCountBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ElectrochemicalBodyConsortium as Consortium
import DASHI.Biology.Levin.ComponentCausalRoleBoundary as CausalRole

------------------------------------------------------------------------
-- Order-of-magnitude cell-count claims are descriptive population estimates,
-- not identity, causal-control, intelligence, or moral-status measures.

record CellCountEstimate : Set where
  field
    humanCellEstimateTrillions : Nat
    bacterialCellEstimateTrillions : Nat
    bodySiteAndSamplingExplicit : Bool
    personAndTimeVariationExplicit : Bool
    estimateUncertaintyExplicit : Bool
    biomassSeparatelyTracked : Bool
    nonbacterialMicrobiotaSeparatelyTracked : Bool

record HostMicrobeCellCountBoundary : Set where
  field
    consortiumBoundary : Consortium.ElectrochemicalBodyConsortiumBoundary
    causalRoleBoundary : CausalRole.ComponentCausalRoleBoundary
    oldTenToOneRuleNotRetained : Bool
    comparableOrderOfMagnitudeAllowed : Bool
    microbialCellsNotMajorityByBodyMass : Bool
    cellNumberNotIdentityWeight : Bool
    cellNumberNotCausalControlWeight : Bool
    cellNumberNotMoralStatusWeight : Bool
    estimateNotUniversalConstant : Bool
    interpretation : String

canonicalCellCountEstimate : CellCountEstimate
canonicalCellCountEstimate = record
  { humanCellEstimateTrillions = 30
  ; bacterialCellEstimateTrillions = 38
  ; bodySiteAndSamplingExplicit = true
  ; personAndTimeVariationExplicit = true
  ; estimateUncertaintyExplicit = true
  ; biomassSeparatelyTracked = true
  ; nonbacterialMicrobiotaSeparatelyTracked = true
  }

canonicalHostMicrobeCellCountBoundary : HostMicrobeCellCountBoundary
canonicalHostMicrobeCellCountBoundary = record
  { consortiumBoundary = Consortium.canonicalElectrochemicalBodyConsortiumBoundary
  ; causalRoleBoundary = CausalRole.canonicalComponentCausalRoleBoundary
  ; oldTenToOneRuleNotRetained = true
  ; comparableOrderOfMagnitudeAllowed = true
  ; microbialCellsNotMajorityByBodyMass = true
  ; cellNumberNotIdentityWeight = true
  ; cellNumberNotCausalControlWeight = true
  ; cellNumberNotMoralStatusWeight = true
  ; estimateNotUniversalConstant = true
  ; interpretation = "Reference host and bacterial cell counts may be of comparable order of magnitude, but estimates vary by person, time, body site, counting method, and organism class; numerical abundance does not determine identity, causal control, intelligence, or moral status"
  }

MoreCellsImpliesMoreControl : Bool
MoreCellsImpliesMoreControl = false

MoreCellsImpliesMoreSelfhood : Bool
MoreCellsImpliesMoreSelfhood = false
