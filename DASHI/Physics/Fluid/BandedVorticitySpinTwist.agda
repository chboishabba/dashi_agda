module DASHI.Physics.Fluid.BandedVorticitySpinTwist where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import DASHI.Foundations.SSPTritCarrier using
  (SSPTrit; sspNegOne; sspZero; sspPosOne)

------------------------------------------------------------------------
-- Candidate-only fluid/codec bridge.
--
-- This module does not claim Navier--Stokes closure.  It records the exact
-- information split required by the CFD experiments:
--
--   low / mid / high scale bands
--   × {-1,0,+1} spin-or-twist carrier
--   × sparse support and optional coarse amplitude
--
-- The fast route keeps aggregate unresolved-band summaries.  The faithful
-- route additionally carries spatially placed signed atoms.  Erasing those
-- atoms gives the fast state, so the two solver modes share one carrier rather
-- than becoming unrelated implementations.


data ScaleBand : Set where
  lowBand : ScaleBand
  midBand : ScaleBand
  highBand : ScaleBand

canonicalBands : List ScaleBand
canonicalBands = lowBand ∷ midBand ∷ highBand ∷ []

record PeriodicSite : Set where
  constructor site
  field
    row : Nat
    column : Nat
open PeriodicSite public

-- FFT differentiation and wrapped neighbourhood operators live on a torus.
-- A non-periodic smoother must not be silently substituted into this lane.
record PeriodicBoundaryContract : Set where
  constructor periodicBoundary
  field
    extent : Nat
    wrap : Nat → Nat
    wrapIsIdempotent : ∀ i → wrap (wrap i) ≡ wrap i
open PeriodicBoundaryContract public

spinSupport : SSPTrit → Bool
spinSupport sspNegOne = true
spinSupport sspZero = false
spinSupport sspPosOne = true

spinOrientation : SSPTrit → SSPTrit
spinOrientation t = t

negativeSpinSupported : spinSupport sspNegOne ≡ true
negativeSpinSupported = refl

neutralSpinUnsupported : spinSupport sspZero ≡ false
neutralSpinUnsupported = refl

positiveSpinSupported : spinSupport sspPosOne ≡ true
positiveSpinSupported = refl

record BandedSpinTwistSample : Set where
  constructor bandedSpinTwist
  field
    sampleBand : ScaleBand
    sampleSite : PeriodicSite
    sampleSpin : SSPTrit
    sampleAmplitudeLevel : Nat
open BandedSpinTwistSample public

-- A sparse vortex/skeleton atom is a supported signed sample with a core scale
-- and circulation proxy. Geometry is represented rather than regenerated from
-- random phase.
record VortexAtom : Set where
  constructor vortexAtom
  field
    atomBand : ScaleBand
    atomSite : PeriodicSite
    atomSpin : SSPTrit
    atomIsSupported : spinSupport atomSpin ≡ true
    atomCoreScale : Nat
    atomCirculationLevel : Nat
open VortexAtom public

record BandEnergySummary : Set where
  constructor bandEnergy
  field
    energyBand : ScaleBand
    energyLevel : Nat
open BandEnergySummary public

record FastResidualState : Set where
  constructor fastResidual
  field
    fastBandEnergy : List BandEnergySummary
    fastSupportFraction : Nat
    fastTextureSeed : Nat
open FastResidualState public

record FaithfulResidualState : Set where
  constructor faithfulResidual
  field
    faithfulBandEnergy : List BandEnergySummary
    faithfulSupportFraction : Nat
    faithfulAtoms : List VortexAtom
open FaithfulResidualState public

-- Both modes retain the same low-band carrier. The difference is only how
-- unresolved mid/high structure is represented.
record LowBandCarrier : Set where
  constructor lowCarrier
  field
    lowCoefficientsDescription : String
    lowSpinTwist : List BandedSpinTwistSample
open LowBandCarrier public

data SolverMode : Set where
  fastMode : SolverMode
  vortexFaithfulMode : SolverMode

record FastSolverState : Set where
  constructor fastState
  field
    fastLowCarrier : LowBandCarrier
    fastResidual : FastResidualState
open FastSolverState public

record VortexFaithfulSolverState : Set where
  constructor vortexFaithfulState
  field
    faithfulLowCarrier : LowBandCarrier
    faithfulResidual : FaithfulResidualState
open VortexFaithfulSolverState public

-- Forgetting vortex placement is an explicit quotient. It preserves aggregate
-- summaries while discarding the atom list and assigning a texture seed.
eraseFaithfulResidual : Nat → FaithfulResidualState → FastResidualState
eraseFaithfulResidual seed r =
  fastResidual
    (faithfulBandEnergy r)
    (faithfulSupportFraction r)
    seed

eraseFaithfulState : Nat → VortexFaithfulSolverState → FastSolverState
eraseFaithfulState seed s =
  fastState
    (faithfulLowCarrier s)
    (eraseFaithfulResidual seed (faithfulResidual s))

erasurePreservesLowCarrier :
  ∀ seed s → fastLowCarrier (eraseFaithfulState seed s) ≡ faithfulLowCarrier s
erasurePreservesLowCarrier seed s = refl

erasurePreservesBandEnergy :
  ∀ seed r → fastBandEnergy (eraseFaithfulResidual seed r) ≡ faithfulBandEnergy r
erasurePreservesBandEnergy seed r = refl

erasurePreservesSupportFraction :
  ∀ seed r →
  fastSupportFraction (eraseFaithfulResidual seed r) ≡
  faithfulSupportFraction r
erasurePreservesSupportFraction seed r = refl

-- Aggregate correctness is available in both modes; trajectory-level vortex
-- identity requires the atom carrier.
data SolverCapability : SolverMode → Set where
  aggregateBandStatistics : SolverCapability fastMode
  aggregateBandStatisticsFaithful : SolverCapability vortexFaithfulMode
  spatialVortexIdentity : SolverCapability vortexFaithfulMode
  signedSkeletonTransport : SolverCapability vortexFaithfulMode

fastModeHasAggregateCapability : SolverCapability fastMode
fastModeHasAggregateCapability = aggregateBandStatistics

faithfulModeHasVortexCapability : SolverCapability vortexFaithfulMode
faithfulModeHasVortexCapability = spatialVortexIdentity

-- Neither a random-phase texture nor a ternary mask alone is identified with a
-- faithful vortex reconstruction.
data ReconstructionClaim : Set where
  aggregateResidualTexture : ReconstructionClaim
  spatiallyPlacedSignedVortices : ReconstructionClaim
  exactContinuumVorticity : ReconstructionClaim

ClaimAvailable : SolverMode → ReconstructionClaim → Set
ClaimAvailable fastMode aggregateResidualTexture = ⊤
ClaimAvailable fastMode spatiallyPlacedSignedVortices = ⊥
ClaimAvailable fastMode exactContinuumVorticity = ⊥
ClaimAvailable vortexFaithfulMode aggregateResidualTexture = ⊤
ClaimAvailable vortexFaithfulMode spatiallyPlacedSignedVortices = ⊤
ClaimAvailable vortexFaithfulMode exactContinuumVorticity = ⊥

fastSpatialVortexPromotionRejected :
  ClaimAvailable fastMode spatiallyPlacedSignedVortices → ⊥
fastSpatialVortexPromotionRejected impossible = impossible

fastExactContinuumPromotionRejected :
  ClaimAvailable fastMode exactContinuumVorticity → ⊥
fastExactContinuumPromotionRejected impossible = impossible

faithfulExactContinuumPromotionRejected :
  ClaimAvailable vortexFaithfulMode exactContinuumVorticity → ⊥
faithfulExactContinuumPromotionRejected impossible = impossible

canonicalInterpretationNotes : List String
canonicalInterpretationNotes =
  "low/mid/high are scale bands, not the ternary values"
  ∷ "-1/0/+1 encode negative twist, unsupported-neutral, and positive twist"
  ∷ "support and sign are retained separately through spinSupport and sampleSpin"
  ∷ "fast mode may preserve aggregate band statistics without vortex identity"
  ∷ "vortex-faithful mode retains sparse signed atoms and skeleton placement"
  ∷ "faithful-to-fast erasure is an explicit quotient"
  ∷ "periodic boundary handling is part of the solver contract"
  ∷ "no continuum Navier--Stokes closure theorem is promoted here"
  ∷ []
