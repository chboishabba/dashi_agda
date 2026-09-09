module DASHI.Physics.GR.UniversalSignedGCrossScaleFingerprintBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact as Source
import DASHI.Physics.GR.SignedNewtonianLimitBidiExact as Newton
import DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact as Wave
import DASHI.Physics.GR.SignedCosmologicalMatterCouplingBidiExact as Cosmology

------------------------------------------------------------------------
-- UNIVERSAL SIGNED-G CROSS-SCALE FINGERPRINT
--
-- A universal negative-G hypothesis is stronger than a local repulsive-force
-- model.  The same coupling sign must be retained across every consumer that
-- claims to instantiate the same gravitational coupling.
------------------------------------------------------------------------

record UniversalSignedGFingerprint : Set where
  constructor universal-signed-g-fingerprint
  field
    universalCouplingSign : Signed.CouplingSign

    localNewtonianSign : Signed.CouplingSign
    waveSourceCouplingSign : Signed.CouplingSign
    cosmologicalMatterCouplingSign : Signed.CouplingSign

    localSignMatchesUniversal :
      localNewtonianSign ≡ universalCouplingSign
    waveSignMatchesUniversal :
      waveSourceCouplingSign ≡ universalCouplingSign
    cosmologySignMatchesUniversal :
      cosmologicalMatterCouplingSign ≡ universalCouplingSign

    localPositiveDensityResponse : Newton.RadialResponseOrientation
    localResponseMatches :
      localPositiveDensityResponse
        ≡ Newton.positiveDensityRadialResponse localNewtonianSign

    waveGenerationSensitivity : Wave.CouplingSignSensitivity
    waveGenerationSensitivityMatches :
      waveGenerationSensitivity
        ≡ Wave.stageSensitivity Wave.sourceGenerationStage

    vacuumPropagationSensitivity : Wave.CouplingSignSensitivity
    vacuumPropagationSensitivityMatches :
      vacuumPropagationSensitivity
        ≡ Wave.stageSensitivity Wave.vacuumPropagationStage

    cosmologicalPositiveDensityMatterTerm :
      Cosmology.CosmologicalMatterTermOrientation
    cosmologicalMatterTermMatches :
      cosmologicalPositiveDensityMatterTerm
        ≡ Cosmology.matterTermOrientation
             cosmologicalMatterCouplingSign
             Source.positiveSource

open UniversalSignedGFingerprint public

------------------------------------------------------------------------
-- Concrete sign-level fingerprints.  These are algebraic/counterfactual
-- fingerprints only; they are not empirical theory receipts.
------------------------------------------------------------------------

positiveGSignFingerprint : UniversalSignedGFingerprint
positiveGSignFingerprint =
  universal-signed-g-fingerprint
    Signed.positiveCoupling
    Signed.positiveCoupling
    Signed.positiveCoupling
    Signed.positiveCoupling
    refl refl refl
    Newton.attractiveTowardPositiveSource refl
    Wave.couplingSignRelevant refl
    Wave.couplingSignNotIdentifiedByThisStage refl
    Cosmology.positiveMatterContribution refl

negativeGSignFingerprint : UniversalSignedGFingerprint
negativeGSignFingerprint =
  universal-signed-g-fingerprint
    Signed.negativeCoupling
    Signed.negativeCoupling
    Signed.negativeCoupling
    Signed.negativeCoupling
    refl refl refl
    Newton.repulsiveAwayFromPositiveSource refl
    Wave.couplingSignRelevant refl
    Wave.couplingSignNotIdentifiedByThisStage refl
    Cosmology.negativeMatterContribution refl

------------------------------------------------------------------------
-- Introspective collision: a local repulsive response alone cannot determine
-- whether the coupling is universally negative or only a local effective law
-- has changed.  Universal sign identity is an additional consumer coordinate.
------------------------------------------------------------------------

data LocalRepulsionFixture : Set where
  universalNegativeGFixture : LocalRepulsionFixture
  localEffectiveRepulsionFixture : LocalRepulsionFixture

data CoarseLocalResponse : Set where
  repulsiveLocalGravityLikeResponse : CoarseLocalResponse

data GlobalSignDecision : Set where
  universalNegativeGDecision localModelOnlyDecision : GlobalSignDecision

coarseLocalObserve : LocalRepulsionFixture → CoarseLocalResponse
coarseLocalObserve _ = repulsiveLocalGravityLikeResponse

globalSignDecision : LocalRepulsionFixture → GlobalSignDecision
globalSignDecision universalNegativeGFixture = universalNegativeGDecision
globalSignDecision localEffectiveRepulsionFixture = localModelOnlyDecision

localRepulsionCollision :
  coarseLocalObserve universalNegativeGFixture
    ≡ coarseLocalObserve localEffectiveRepulsionFixture
localRepulsionCollision = refl

localRepulsionDoesNotDetermineUniversalGSign :
  globalSignDecision universalNegativeGFixture
    ≡ globalSignDecision localEffectiveRepulsionFixture → ⊥
localRepulsionDoesNotDetermineUniversalGSign ()

record UniversalSignedGCrossScaleBoundary : Set where
  constructor universal-signed-g-cross-scale-boundary
  field
    localRepulsiveObservationAutomaticallyMeansUniversalNegativeG : Bool
    universalNegativeGRequiresSameSignAcrossScales : Bool
    vacuumGWPropagationAlonePaysUniversalSignIdentity : Bool
    waveSourceGenerationMustRespectUniversalSign : Bool
    cosmologicalMatterCouplingMustRespectUniversalSign : Bool
    localNewtonianResponseMustRespectUniversalSign : Bool
    oneScaleFitAutomaticallyPromotesUniversalNegativeG : Bool
    crossScaleTensionMayRejectUniversalSignHypothesis : Bool

canonicalUniversalSignedGCrossScaleBoundary : UniversalSignedGCrossScaleBoundary
canonicalUniversalSignedGCrossScaleBoundary =
  universal-signed-g-cross-scale-boundary false true false true true true false true
