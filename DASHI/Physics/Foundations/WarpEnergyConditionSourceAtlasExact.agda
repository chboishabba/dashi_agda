module DASHI.Physics.Foundations.WarpEnergyConditionSourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- WARP-ENERGY-CONDITION SOURCE ATLAS
--
-- Claim-bounded source ledger only.  This module does not construct a warp
-- device, identify a physical stress-energy source, or promote any subluminal
-- metric construction into FTL transport.
--
-- Source A: Santiago, Schuster & Visser, Phys. Rev. D 105, 064038 (2022),
-- DOI 10.1103/PhysRevD.105.064038.  Their result concerns generic physically
-- reasonable warp drives in the framework analysed and finds unavoidable
-- standard energy-condition violations (with NEC violation under the stated
-- subsidiary conditions).
--
-- Source B: Fuchs et al., Classical and Quantum Gravity 41, 095013 (2024),
-- DOI 10.1088/1361-6382/ad26aa.  They numerically construct a constant-
-- velocity SUBLUMINAL warp spacetime with a positive-ADM-mass matter shell
-- satisfying the standard energy conditions.
--
-- These claims are compatible because their quantified classes/assumptions
-- are not identical.  Neither source pays a physical superluminal drive.
------------------------------------------------------------------------

record WarpSourceClaim : Set where
  constructor warp-source-claim
  field
    doi : String
    claimClass : String
    velocityRegime : String
    standardGREnergyConditionClaim : String
    physicalMatterRealizationMeasured : Bool
    causalSuperluminalTransportMeasured : Bool

open WarpSourceClaim public

santiagoSchusterVisser2022 : WarpSourceClaim
santiagoSchusterVisser2022 =
  warp-source-claim
    "10.1103/PhysRevD.105.064038"
    "generic physically reasonable warp drives in the analysed standard-GR framework"
    "generic; theorem is not a physical FTL experiment"
    "WEC/SEC/DEC violation unavoidable in analysed class; NEC violation under plausible subsidiary conditions"
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
    genericPhysicallyReasonableWarpEnergyConditionViolationSourcePaid : Bool
    constantVelocitySubluminalPositiveEnergyConstructionSourcePaid : Bool
    quantifiedClassesKeptDistinct : Bool
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
    true true true
    false false false false false false false

record WarpEnergyConditionAttributionBoundary : Set where
  constructor warp-energy-condition-attribution-boundary
  field
    santiagoSchusterVisserOwnGenericEnergyConditionResult : Bool
    fuchsEtAlOwnSubluminalPositiveEnergyConstruction : Bool
    dashiOwnsTypedClaimSeparationAndNonPromotion : Bool
    crossSourceCompositionTransfersNoEmpiricalAuthority : Bool

open WarpEnergyConditionAttributionBoundary public

canonicalWarpEnergyConditionAttributionBoundary : WarpEnergyConditionAttributionBoundary
canonicalWarpEnergyConditionAttributionBoundary =
  warp-energy-condition-attribution-boundary true true true true
