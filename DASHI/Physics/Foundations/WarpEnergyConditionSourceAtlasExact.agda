module DASHI.Physics.Foundations.WarpEnergyConditionSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- WARP-ENERGY-CONDITION SOURCE ATLAS
--
-- Claim-bounded source ledger only.  This module does not construct a warp
-- device, identify a physical stress-energy source, or promote any metric
-- construction into a realised FTL transport system.
------------------------------------------------------------------------

record WarpSourceClaim : Set where
  constructor warp-source-claim
  field
    doi : String
    claimClass : String
    velocityRegime : String
    energyClaim : String
    physicalMatterRealizationMeasured : Bool
    causalSuperluminalTransportMeasured : Bool

open WarpSourceClaim public

fellHeisenberg2021 : WarpSourceClaim
fellHeisenberg2021 =
  warp-source-claim
    "10.1088/1361-6382/ac0e47"
    "positive-energy construction using hidden geometric structures"
    "contains a superluminal solitonic spacetime example"
    "positive semidefinite Eulerian energy density is constructed; this is not by itself a proof of WEC/NEC for all observers"
    false false

santiagoSchusterVisser2022 : WarpSourceClaim
santiagoSchusterVisser2022 =
  warp-source-claim
    "10.1103/PhysRevD.105.064038"
    "generic physically reasonable warp drives in the analysed standard-GR framework"
    "generic; theorem is not a physical FTL experiment"
    "WEC/SEC/DEC violation unavoidable in analysed class; NEC violation under plausible subsidiary conditions; positivity for Eulerian observers is insufficient to establish WEC"
    false false

fuchsEtAl2024 : WarpSourceClaim
fuchsEtAl2024 =
  warp-source-claim
    "10.1088/1361-6382/ad26aa"
    "numerically generated constant-velocity warp spacetime with stable matter shell and positive ADM mass"
    "subluminal"
    "constructed solution satisfies the standard energy conditions"
    false false

record WarpEnergyConditionSourceAtlas : Set where
  constructor warp-energy-condition-source-atlas
  field
    superluminalPositiveEulerianEnergyConstructionSourcePaid : Bool
    genericPhysicallyReasonableWarpEnergyConditionViolationSourcePaid : Bool
    constantVelocitySubluminalPositiveEnergyConstructionSourcePaid : Bool
    quantifiedClassesAndObserverClaimsKeptDistinct : Bool
    positiveEulerianEnergyCountsAsFullWEC : Bool
    positiveEulerianEnergyCountsAsNEC : Bool
    subluminalPositiveEnergyConstructionCountsAsFTL : Bool
    sourceTheoremCountsAsPhysicalWarpDevice : Bool
    positiveEnergySubluminalConstructionRefutesGenericStandardGRResult : Bool
    superluminalPositiveEnergyPhysicalSourcePaid : Bool
    physicalStressEnergySourceBuilt : Bool
    warpStabilityBackreactionExperimentPaid : Bool
    causalSuperluminalTransportExperimentPaid : Bool

open WarpEnergyConditionSourceAtlas public

canonicalWarpEnergyConditionSourceAtlas : WarpEnergyConditionSourceAtlas
canonicalWarpEnergyConditionSourceAtlas =
  warp-energy-condition-source-atlas
    true true true true
    false false false false false false false false false

record WarpEnergyConditionAttributionBoundary : Set where
  constructor warp-energy-condition-attribution-boundary
  field
    fellHeisenbergOwnPositiveEulerianEnergyConstruction : Bool
    santiagoSchusterVisserOwnGenericEnergyConditionResult : Bool
    fuchsEtAlOwnSubluminalPositiveEnergyConstruction : Bool
    dashiOwnsTypedClaimSeparationAndNonPromotion : Bool
    crossSourceCompositionTransfersNoEmpiricalAuthority : Bool

open WarpEnergyConditionAttributionBoundary public

canonicalWarpEnergyConditionAttributionBoundary : WarpEnergyConditionAttributionBoundary
canonicalWarpEnergyConditionAttributionBoundary =
  warp-energy-condition-attribution-boundary true true true true true
