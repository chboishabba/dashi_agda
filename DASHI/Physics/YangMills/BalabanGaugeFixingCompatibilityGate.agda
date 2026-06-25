module DASHI.Physics.YangMills.BalabanGaugeFixingCompatibilityGate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

-- ── GaugeFixingCompatibilityGate ────────────────────────────────────
-- Per 2602.0096 §7.6, the OS/Wightman route does NOT require smooth-gauge
-- fixing.  Gribov singularities are zero-capacity "blind spots" for the
-- RCD* diffusers — subsets of codimension ≥ 2 in A have zero capacity.
-- The Bałaban RG handles gauge via small/large-field cutoffs and
-- Faddeev-Popov determinant management at the lattice level.
--
-- Therefore:
--   gaugeFixingCompatibilityClosed = true  [OS route — closed]
--   alternateBRSTRouteAvailable    = false [separate gate, out of scope]
--
-- Block/carrier level (closed):
--   BruhatTitsCarrierGaugeFixingReceipt    — unique rep basis, coordinate roles
--   YMSmallFieldSurvivalAuthority           — Faddeev-Popov Jacobian bound, orbit measure
--   ClaySprintEightyOne                     — block convention compatibility
--   LieGaugeTheoryParity                    — gauge-fixing interface shape recorded
--   radiationGaugeOSCompatible              — Osterwalder–Seiler radiation gauge works at lattice level (2602.0088 §8.1)
--   latticeGaugeFixingForOS                 — Wilson action supports gauge fixing for OS axioms (§8.1)
--
-- Alternate BRST route (open, out of scope):
--   Singer global section obstruction       — not required for OS route
--   Continuum Gribov copies                 — zero-capacity blind spots (§7.6)
--   Continuum gauge slice                    — not constructed (OS doesn't need it)
--   BRST positive Hilbert OS3                — separate construction path
--   Continuum gauge-fixing authority         — BRST route specifically, not OS

record GaugeFixingCompatibilityGate : Set where
  field
    -- Block/carrier level (closed)
    blockGaugeFixingConventionAvailable    : Bool
    faddeevPopovJacobianBoundAvailable     : Bool
    gaugeOrbitMeasurePreserved             : Bool
    carrierUniqueRepBasisRecorded          : Bool
    gate3LiftObligationPreserved           : Bool
    radiationGaugeOSCompatible             : Bool
    latticeGaugeFixingForOS                : Bool

    -- Alternate BRST route (open, out of scope for OS)
    brstContinuumGaugeSliceConstructed         : Bool
    brstSingerGlobalSectionObstructionDefeated : Bool
    brstContinuumGribovCopiesResolved          : Bool
    brstGlobalSmoothGaugeFixingAvailable       : Bool
    brstPositiveHilbertOS3Available            : Bool
    brstGaugeFixingAuthorized                  : Bool

    -- Alternate BRST route aggregate (separate gate out of scope)
    alternateBRSTRouteAvailable            : Bool

    -- Assembly
    gaugeFixingCompatibilityClosed         : Bool

    blockGaugeFixingConventionAvailableIsTrue    : blockGaugeFixingConventionAvailable ≡ true
    faddeevPopovJacobianBoundAvailableIsTrue     : faddeevPopovJacobianBoundAvailable ≡ true
    gaugeOrbitMeasurePreservedIsTrue             : gaugeOrbitMeasurePreserved ≡ true
    carrierUniqueRepBasisRecordedIsTrue          : carrierUniqueRepBasisRecorded ≡ true
    gate3LiftObligationPreservedIsTrue           : gate3LiftObligationPreserved ≡ true
    radiationGaugeOSCompatibleIsTrue             : radiationGaugeOSCompatible ≡ true
    latticeGaugeFixingForOSIsTrue                : latticeGaugeFixingForOS ≡ true

    brstContinuumGaugeSliceConstructedIsFalse         : brstContinuumGaugeSliceConstructed ≡ false
    brstSingerGlobalSectionObstructionDefeatedIsFalse  : brstSingerGlobalSectionObstructionDefeated ≡ false
    brstContinuumGribovCopiesResolvedIsFalse           : brstContinuumGribovCopiesResolved ≡ false
    brstGlobalSmoothGaugeFixingAvailableIsFalse        : brstGlobalSmoothGaugeFixingAvailable ≡ false
    brstPositiveHilbertOS3AvailableIsFalse              : brstPositiveHilbertOS3Available ≡ false
    brstGaugeFixingAuthorizedIsFalse                    : brstGaugeFixingAuthorized ≡ false

    alternateBRSTRouteAvailableIsFalse                : alternateBRSTRouteAvailable ≡ false

    gaugeFixingCompatibilityClosedIsTrue         : gaugeFixingCompatibilityClosed ≡ true

    blockLevelSources : String
    blockLevelSourcesIsCanonical :
      blockLevelSources ≡
      "block-gauge-fixing: BruhatTitsCarrierGaugeFixingReceipt, YMSmallFieldSurvivalAuthority, ClaySprintEightyOne blockGaugeFixingConventionCompatibility, Eriksson 2602.0088 §8.1 radiationGaugeOSCompatible + latticeGaugeFixingForOS"
    osRouteNote : String
    osRouteNoteIsCanonical :
      osRouteNote ≡
      "Per 2602.0096 §7.6: OS route does not require smooth-gauge fixing; Gribov singularities are zero-capacity blind spots for RCD* diffusers; Bałaban RG handles gauge non-perturbatively. gaugeFixingCompatibilityClosed = true for OS route."
    brstRouteSources : String
    brstRouteSourcesIsCanonical :
      brstRouteSources ≡
      "alternateBRSTRouteAvailable = false: Singer obstruction, continuum Gribov, global smooth slice, BRST positive-Hilbert OS3, and gauge-fixing authority are all false — separate construction path, out of scope for OS/Wightman route"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentGaugeFixingCompatibilityGate : GaugeFixingCompatibilityGate
currentGaugeFixingCompatibilityGate = record
  { blockGaugeFixingConventionAvailable    = true
  ; faddeevPopovJacobianBoundAvailable     = true
  ; gaugeOrbitMeasurePreserved             = true
  ; carrierUniqueRepBasisRecorded          = true
  ; gate3LiftObligationPreserved           = true
  ; radiationGaugeOSCompatible             = true
  ; latticeGaugeFixingForOS                = true
  ; brstContinuumGaugeSliceConstructed         = false
  ; brstSingerGlobalSectionObstructionDefeated = false
  ; brstContinuumGribovCopiesResolved          = false
  ; brstGlobalSmoothGaugeFixingAvailable       = false
  ; brstPositiveHilbertOS3Available            = false
  ; brstGaugeFixingAuthorized                  = false
  ; alternateBRSTRouteAvailable            = false
  ; gaugeFixingCompatibilityClosed         = true
  ; blockGaugeFixingConventionAvailableIsTrue    = refl
  ; faddeevPopovJacobianBoundAvailableIsTrue     = refl
  ; gaugeOrbitMeasurePreservedIsTrue             = refl
  ; carrierUniqueRepBasisRecordedIsTrue          = refl
  ; gate3LiftObligationPreservedIsTrue           = refl
  ; radiationGaugeOSCompatibleIsTrue             = refl
  ; latticeGaugeFixingForOSIsTrue                = refl
  ; brstContinuumGaugeSliceConstructedIsFalse         = refl
  ; brstSingerGlobalSectionObstructionDefeatedIsFalse  = refl
  ; brstContinuumGribovCopiesResolvedIsFalse           = refl
  ; brstGlobalSmoothGaugeFixingAvailableIsFalse        = refl
  ; brstPositiveHilbertOS3AvailableIsFalse              = refl
  ; brstGaugeFixingAuthorizedIsFalse                    = refl
  ; alternateBRSTRouteAvailableIsFalse                = refl
  ; gaugeFixingCompatibilityClosedIsTrue         = refl
  ; blockLevelSources =
      "block-gauge-fixing: BruhatTitsCarrierGaugeFixingReceipt, YMSmallFieldSurvivalAuthority, ClaySprintEightyOne blockGaugeFixingConventionCompatibility, Eriksson 2602.0088 §8.1 radiationGaugeOSCompatible + latticeGaugeFixingForOS"
  ; blockLevelSourcesIsCanonical = refl
  ; osRouteNote =
      "Per 2602.0096 §7.6: OS route does not require smooth-gauge fixing; Gribov singularities are zero-capacity blind spots for RCD* diffusers; Bałaban RG handles gauge non-perturbatively. gaugeFixingCompatibilityClosed = true for OS route."
  ; osRouteNoteIsCanonical = refl
  ; brstRouteSources =
      "alternateBRSTRouteAvailable = false: Singer obstruction, continuum Gribov, global smooth slice, BRST positive-Hilbert OS3, and gauge-fixing authority are all false — separate construction path, out of scope for OS/Wightman route"
  ; brstRouteSourcesIsCanonical = refl
  ; noClayPromotion = refl
  }
