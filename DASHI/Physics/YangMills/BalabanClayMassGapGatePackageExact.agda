module DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact where

------------------------------------------------------------------------
-- DASHI CLAY-FACING GATES
--
-- M1 physical-scale clustering;
-- M2 dense-core spectral exclusion;
-- M3 local noncollapse;
-- M4 positivity-compatible RG, by exact OS pullback or transfer intertwining;
-- M5 optional spectral-edge detectability;
-- M6 spectral/ultraviolet compatibility.
--
-- The package keeps the propositions independent.  In particular M2 does not
-- consume M5, and M4 is a genuine disjunction between two complete routes.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayPhysicalScaleExponentExact
import DASHI.Physics.YangMills.BalabanClayDenseCoreSpectralGapExact
import DASHI.Physics.YangMills.BalabanClayExactOSPullbackRecombinationExact
import DASHI.Physics.YangMills.BalabanClayObservableGapEdgeExact
import DASHI.Physics.YangMills.BalabanClaySpectralUVCompatibilityExact

infixr 4 _or_
data _or_ (A B : Set) : Set where
  leftRoute : A → A or B
  rightRoute : B → A or B

record ClayMassGapGatePropositions : Set₁ where
  field
    M1PhysicalScaleClustering : Set
    M2DenseCoreSpectralExclusion : Set
    M3LocalNoncollapse : Set
    M4ExactOSPullback : Set
    M4TransferIntertwining : Set
    M5ObservableDetectsGapEdge : Set
    M6SpectralUVCompatibility : Set

open ClayMassGapGatePropositions public

record MandatoryClayMassGapGates
    (gates : ClayMassGapGatePropositions) : Set₁ where
  field
    m1 : M1PhysicalScaleClustering gates
    m2 : M2DenseCoreSpectralExclusion gates
    m3 : M3LocalNoncollapse gates
    m4 : M4ExactOSPullback gates or M4TransferIntertwining gates
    m6 : M6SpectralUVCompatibility gates

open MandatoryClayMassGapGates public

record SharpMassIdentification
    (gates : ClayMassGapGatePropositions) : Set₁ where
  field
    mandatory : MandatoryClayMassGapGates gates
    m5 : M5ObservableDetectsGapEdge gates

open SharpMassIdentification public

assembleMandatoryClayMassGapGates :
  ∀ gates →
  M1PhysicalScaleClustering gates →
  M2DenseCoreSpectralExclusion gates →
  M3LocalNoncollapse gates →
  (M4ExactOSPullback gates or M4TransferIntertwining gates) →
  M6SpectralUVCompatibility gates →
  MandatoryClayMassGapGates gates
assembleMandatoryClayMassGapGates gates gate1 gate2 gate3 gate4 gate6 = record
  { m1 = gate1
  ; m2 = gate2
  ; m3 = gate3
  ; m4 = gate4
  ; m6 = gate6
  }

addOptionalSpectralEdgeIdentification :
  ∀ {gates} →
  MandatoryClayMassGapGates gates →
  M5ObservableDetectsGapEdge gates →
  SharpMassIdentification gates
addOptionalSpectralEdgeIdentification mandatoryGates gate5 = record
  { mandatory = mandatoryGates
  ; m5 = gate5
  }

massGapGateSeparationLevel : ProofLevel
massGapGateSeparationLevel = machineChecked

physicalGateProducersLevel : ProofLevel
physicalGateProducersLevel = conditional
