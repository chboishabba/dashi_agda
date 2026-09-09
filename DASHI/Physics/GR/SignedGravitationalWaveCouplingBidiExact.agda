module DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed

------------------------------------------------------------------------
-- SIGNED-G GRAVITATIONAL-WAVE BIDI
--
-- The existing GravitationalWaveLaw exposes linearised propagation through
-- background metric + perturbation + gauge; its linearise operation has no
-- explicit matter-coupling argument.  Therefore a vacuum-propagation observer
-- alone cannot identify the sign of the Einstein matter coupling.
--
-- Source generation is a different stage: a sourced perturbation and source
-- dynamics may depend on G.  Those stages must not be collapsed.
------------------------------------------------------------------------

data WaveCouplingStage : Set where
  sourceGenerationStage : WaveCouplingStage
  vacuumPropagationStage : WaveCouplingStage
  detectorProjectionStage : WaveCouplingStage

data CouplingSignSensitivity : Set where
  couplingSignRelevant : CouplingSignSensitivity
  couplingSignNotIdentifiedByThisStage : CouplingSignSensitivity

stageSensitivity : WaveCouplingStage → CouplingSignSensitivity
stageSensitivity sourceGenerationStage = couplingSignRelevant
stageSensitivity vacuumPropagationStage = couplingSignNotIdentifiedByThisStage
stageSensitivity detectorProjectionStage = couplingSignNotIdentifiedByThisStage

------------------------------------------------------------------------
-- Exact introspective collision for the vacuum-propagation observer.
------------------------------------------------------------------------

data VacuumPropagationFixture : Set where
  positiveGCouplingFixture : VacuumPropagationFixture
  negativeGCouplingFixture : VacuumPropagationFixture

fixtureCoupling : VacuumPropagationFixture → Signed.CouplingSign
fixtureCoupling positiveGCouplingFixture = Signed.positiveCoupling
fixtureCoupling negativeGCouplingFixture = Signed.negativeCoupling

data VacuumPropagationObservation : Set where
  sameVacuumPropagationLaw : VacuumPropagationObservation

coarseVacuumPropagationObserver :
  VacuumPropagationFixture → VacuumPropagationObservation
coarseVacuumPropagationObserver _ = sameVacuumPropagationLaw

vacuumPropagationCollision :
  coarseVacuumPropagationObserver positiveGCouplingFixture
    ≡ coarseVacuumPropagationObserver negativeGCouplingFixture
vacuumPropagationCollision = refl

record RefinedWaveCouplingObserver : Set where
  constructor refined-wave-coupling-observer
  field
    couplingSign : Signed.CouplingSign
    stage : WaveCouplingStage

refinedWaveObserve : VacuumPropagationFixture → RefinedWaveCouplingObserver
refinedWaveObserve fixture =
  refined-wave-coupling-observer (fixtureCoupling fixture) vacuumPropagationStage

refinedWaveFixturesDistinct :
  refinedWaveObserve positiveGCouplingFixture
    ≡ refinedWaveObserve negativeGCouplingFixture → ⊥
refinedWaveFixturesDistinct ()

------------------------------------------------------------------------
-- Reuse marker: attach to the existing wave-law carrier.
------------------------------------------------------------------------

record SignedGravitationalWaveProbe
    (law : Laws.EinsteinGravityLaw)
    (wave : Laws.GravitationalWaveLaw law) : Set₁ where
  constructor signed-gravitational-wave-probe
  field
    couplingSign : Signed.CouplingSign
    sourceGenerationCarrier : Set
    sourceGenerationReceipt : sourceGenerationCarrier
    usesExistingWaveEquation : Laws.GravitationalWaveLaw.WaveEquation wave → Set
    usesExistingObservableStrain : Laws.GravitationalWaveLaw.ObservableStrain wave → Set
    sameBackgroundForSignComparison : Bool
    samePerturbationForVacuumPropagationComparison : Bool
    sourceDynamicsReSolvedForCouplingSign : Bool

open SignedGravitationalWaveProbe public

record SignedGravitationalWaveBoundary : Set where
  constructor signed-gravitational-wave-boundary
  field
    vacuumPropagationObserverAloneDeterminesMatterCouplingSign : Bool
    sourceGenerationMayDependOnCouplingSign : Bool
    detectorStrainAloneDeterminesCouplingSign : Bool
    sameVacuumWaveEquationImpliesSameSourceTheory : Bool
    negativeGAutomaticallyMeansOppositeObservedStrain : Bool
    frozenSourceAmplitudeSignFlipEqualsSelfConsistentNegativeGBinary : Bool
    sourceDynamicsMustBeReSolvedBeforePhysicalNegativeGWavePrediction : Bool
    wavePropagationAgreementCanConstrainButNotIdentifyNegativeG : Bool

canonicalSignedGravitationalWaveBoundary : SignedGravitationalWaveBoundary
canonicalSignedGravitationalWaveBoundary =
  signed-gravitational-wave-boundary false true false false false false true true
