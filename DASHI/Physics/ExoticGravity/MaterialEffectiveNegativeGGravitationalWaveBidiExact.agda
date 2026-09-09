module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGGravitationalWaveBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact as Wave
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact as Polarization
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Material

------------------------------------------------------------------------
-- MATERIAL-EFFECTIVE NEGATIVE G x GRAVITATIONAL WAVES
--
-- A material-scoped effective coupling may enter source generation only through
-- an explicit source/radiative mapping.  Scope alone does not rewrite vacuum
-- propagation, plus/cross polarization basis, detector response, or waveform
-- sign.  This is a DASHI internal derived adapter, not an external source claim.
------------------------------------------------------------------------

data MaterialWaveEffectStage : Set where
  sourceGenerationEffect : MaterialWaveEffectStage
  vacuumPropagationEffect : MaterialWaveEffectStage
  detectorProjectionEffect : MaterialWaveEffectStage
  polarizationBasisEffect : MaterialWaveEffectStage

data MaterialWaveEffectStatus : Set where
  candidateWithExplicitMapping : MaterialWaveEffectStatus
  notImpliedByMaterialScopeAlone : MaterialWaveEffectStatus

statusForStage : MaterialWaveEffectStage → MaterialWaveEffectStatus
statusForStage sourceGenerationEffect = candidateWithExplicitMapping
statusForStage vacuumPropagationEffect = notImpliedByMaterialScopeAlone
statusForStage detectorProjectionEffect = notImpliedByMaterialScopeAlone
statusForStage polarizationBasisEffect = notImpliedByMaterialScopeAlone

record MaterialEffectiveGWaveGenerationHypothesis : Set₁ where
  constructor material-effective-g-wave-generation-hypothesis
  field
    scopedCoupling : Scope.ScopedSignedCouplingHypothesis
    scopeIsMaterialEffective :
      Scope.couplingScope scopedCoupling ≡ Scope.materialEffectiveCoupling
    regimeIsNonOrdinary :
      Scope.materialRegime scopedCoupling ≡ Material.ordinaryRegime → ⊥

    SourceToRadiativeMapping : Set
    sourceToRadiativeMapping : SourceToRadiativeMapping

    SourceDynamicsReceipt : Set
    sourceDynamicsReceipt : SourceDynamicsReceipt

    waveStage : Wave.WaveCouplingStage
    waveStageIsGeneration : waveStage ≡ Wave.sourceGenerationStage

open MaterialEffectiveGWaveGenerationHypothesis public

------------------------------------------------------------------------
-- Introspective collision: a coarse "GW effect" label does not tell us whether
-- the hypothesized modification is at generation or propagation.
------------------------------------------------------------------------

data WaveScopeFixture : Set where
  generationFixture propagationFixture : WaveScopeFixture

data CoarseWaveEffect : Set where
  gravitationalWaveDifference : CoarseWaveEffect

coarseObserve : WaveScopeFixture → CoarseWaveEffect
coarseObserve _ = gravitationalWaveDifference

stageDecision : WaveScopeFixture → MaterialWaveEffectStage
stageDecision generationFixture = sourceGenerationEffect
stageDecision propagationFixture = vacuumPropagationEffect

coarseCollision : coarseObserve generationFixture ≡ coarseObserve propagationFixture
coarseCollision = refl

coarseWaveDifferenceDoesNotDetermineStage :
  stageDecision generationFixture ≡ stageDecision propagationFixture → ⊥
coarseWaveDifferenceDoesNotDetermineStage ()

------------------------------------------------------------------------
-- Polarization/sign collision retained explicitly.
------------------------------------------------------------------------

data MaterialWaveSignFixture : Set where
  positiveCouplingNegativeSample negativeEffectiveCouplingNegativeSample : MaterialWaveSignFixture

sampleSign : MaterialWaveSignFixture → Polarization.WaveformAmplitudeSign
sampleSign _ = Polarization.negativeWaveformAmplitude

scopeDecision : MaterialWaveSignFixture → Scope.CouplingScope
scopeDecision positiveCouplingNegativeSample = Scope.universalNewtonCoupling
scopeDecision negativeEffectiveCouplingNegativeSample = Scope.materialEffectiveCoupling

sameNegativeSampleAcrossScopes :
  sampleSign positiveCouplingNegativeSample
    ≡ sampleSign negativeEffectiveCouplingNegativeSample
sameNegativeSampleAcrossScopes = refl

negativeSampleDoesNotDetermineCouplingScope :
  scopeDecision positiveCouplingNegativeSample
    ≡ scopeDecision negativeEffectiveCouplingNegativeSample → ⊥
negativeSampleDoesNotDetermineCouplingScope ()

------------------------------------------------------------------------
-- Attribution: internal theorem lineage, no citation cargo-cult.
------------------------------------------------------------------------

attributionShape : Shape.RequiredAttributionShape
attributionShape = Shape.requiredAttributionShape Shape.internalDerivedTheorem

record MaterialEffectiveGWaveBoundary : Set where
  constructor material-effective-g-wave-boundary
  field
    materialEffectiveNegativeGAutomaticallyChangesWaveGeneration : Bool
    explicitSourceToRadiativeMappingRequired : Bool
    sourceDynamicsReceiptRequired : Bool
    materialEffectiveNegativeGAutomaticallyChangesVacuumPropagation : Bool
    materialEffectiveNegativeGAutomaticallyChangesPolarizationBasis : Bool
    materialEffectiveNegativeGAutomaticallyFlipsObservedWaveformSign : Bool
    negativeWaveformSampleDeterminesMaterialEffectiveCoupling : Bool
    vacuumPropagationAgreementRejectsEveryMaterialEffectiveSourceModel : Bool
    internalDerivedAdapterNeedsFreshExternalCitation : Bool

canonicalMaterialEffectiveGWaveBoundary : MaterialEffectiveGWaveBoundary
canonicalMaterialEffectiveGWaveBoundary =
  material-effective-g-wave-boundary
    false true true false false false false false false
