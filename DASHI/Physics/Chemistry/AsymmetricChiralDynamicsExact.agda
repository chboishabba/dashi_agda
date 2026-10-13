module DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- GENERIC MIRROR-EQUIVARIANT DYNAMICS
--
-- This owner isolates the reusable mathematical shape behind asymmetric
-- amplification.  It is deliberately chemistry-neutral: a state space has an
-- involutive mirror and a step law commuting with that mirror.  The law may be
-- symmetric even when individual trajectories are not.
------------------------------------------------------------------------

record MirrorEquivariantDynamics : Set₁ where
  constructor mirrorEquivariantDynamics
  field
    State : Set
    mirror : State → State
    step : State → State
    mirrorInvolutive : (x : State) → mirror (mirror x) ≡ x
    stepMirrorEquivariant : (x : State) → step (mirror x) ≡ mirror (step x)

open MirrorEquivariantDynamics public

------------------------------------------------------------------------
-- FINITE CHIRAL AMPLIFICATION FIXTURE
--
-- racemic is mirror fixed.  The left/right seeds are exchanged by mirror.
-- One step amplifies a seed into a branch-selected state.  The amplified
-- states are stable under this finite step.  This proves the logical shape
-- "symmetric law != symmetric realised state" without pretending to be a
-- quantitative kinetic model of the Kagan or Soai experiments.
------------------------------------------------------------------------

data ChiralBiasState : Set where
  leftAmplified : ChiralBiasState
  leftSeed      : ChiralBiasState
  racemic       : ChiralBiasState
  rightSeed     : ChiralBiasState
  rightAmplified : ChiralBiasState

mirrorBias : ChiralBiasState → ChiralBiasState
mirrorBias leftAmplified = rightAmplified
mirrorBias leftSeed = rightSeed
mirrorBias racemic = racemic
mirrorBias rightSeed = leftSeed
mirrorBias rightAmplified = leftAmplified

mirrorBiasInvolutive : (x : ChiralBiasState) → mirrorBias (mirrorBias x) ≡ x
mirrorBiasInvolutive leftAmplified = refl
mirrorBiasInvolutive leftSeed = refl
mirrorBiasInvolutive racemic = refl
mirrorBiasInvolutive rightSeed = refl
mirrorBiasInvolutive rightAmplified = refl

amplifyBias : ChiralBiasState → ChiralBiasState
amplifyBias leftAmplified = leftAmplified
amplifyBias leftSeed = leftAmplified
amplifyBias racemic = racemic
amplifyBias rightSeed = rightAmplified
amplifyBias rightAmplified = rightAmplified

amplifyMirrorEquivariant :
  (x : ChiralBiasState) →
  amplifyBias (mirrorBias x) ≡ mirrorBias (amplifyBias x)
amplifyMirrorEquivariant leftAmplified = refl
amplifyMirrorEquivariant leftSeed = refl
amplifyMirrorEquivariant racemic = refl
amplifyMirrorEquivariant rightSeed = refl
amplifyMirrorEquivariant rightAmplified = refl

finiteChiralDynamics : MirrorEquivariantDynamics
finiteChiralDynamics =
  mirrorEquivariantDynamics
    ChiralBiasState
    mirrorBias
    amplifyBias
    mirrorBiasInvolutive
    amplifyMirrorEquivariant

racemicMirrorFixed : mirrorBias racemic ≡ racemic
racemicMirrorFixed = refl

racemicDynamicallyFixed : amplifyBias racemic ≡ racemic
racemicDynamicallyFixed = refl

leftAmplifiedFixed : amplifyBias leftAmplified ≡ leftAmplified
leftAmplifiedFixed = refl

rightAmplifiedFixed : amplifyBias rightAmplified ≡ rightAmplified
rightAmplifiedFixed = refl

leftSeedAmplifies : amplifyBias leftSeed ≡ leftAmplified
leftSeedAmplifies = refl

rightSeedAmplifies : amplifyBias rightSeed ≡ rightAmplified
rightSeedAmplifies = refl

------------------------------------------------------------------------
-- Finite strength code: exact witness that the seed and amplified state are
-- distinct in magnitude.  This is a discrete amplification certificate, not a
-- continuous enantiomeric-excess calibration.
------------------------------------------------------------------------

biasMagnitudeCode : ChiralBiasState → Nat
biasMagnitudeCode leftAmplified = 2
biasMagnitudeCode leftSeed = 1
biasMagnitudeCode racemic = 0
biasMagnitudeCode rightSeed = 1
biasMagnitudeCode rightAmplified = 2

leftSeedMagnitude : biasMagnitudeCode leftSeed ≡ 1
leftSeedMagnitude = refl

leftAmplifiedMagnitude : biasMagnitudeCode (amplifyBias leftSeed) ≡ 2
leftAmplifiedMagnitude = refl

rightSeedMagnitude : biasMagnitudeCode rightSeed ≡ 1
rightSeedMagnitude = refl

rightAmplifiedMagnitude : biasMagnitudeCode (amplifyBias rightSeed) ≡ 2
rightAmplifiedMagnitude = refl

------------------------------------------------------------------------
-- Dynamic non-factorisation through an over-coarse observer.
--
-- The coarse observer forgets handedness.  A future branch-sensitive consumer
-- distinguishes the two seed states after the same mirror-equivariant step.
-- Therefore predictive dynamics for that consumer cannot factor through this
-- coarse observation.  This upgrades a static separating-pair pattern into a
-- future-sufficiency obstruction.
------------------------------------------------------------------------

data CoarseChemicalChart : Set where
  sameCompositionConnectivityCharge : CoarseChemicalChart

data FutureBranchReadout : Set where
  futureLeft : FutureBranchReadout
  futureRacemic : FutureBranchReadout
  futureRight : FutureBranchReadout

coarseChemicalChart : ChiralBiasState → CoarseChemicalChart
coarseChemicalChart _ = sameCompositionConnectivityCharge

futureBranch : ChiralBiasState → FutureBranchReadout
futureBranch leftAmplified = futureLeft
futureBranch leftSeed = futureLeft
futureBranch racemic = futureRacemic
futureBranch rightSeed = futureRight
futureBranch rightAmplified = futureRight

futureAfterStep : ChiralBiasState → FutureBranchReadout
futureAfterStep x = futureBranch (amplifyBias x)

sameCoarseSeeds : coarseChemicalChart leftSeed ≡ coarseChemicalChart rightSeed
sameCoarseSeeds = refl

futureSeedsSeparate : futureAfterStep leftSeed ≡ futureAfterStep rightSeed → ⊥
futureSeedsSeparate ()

record FutureFactorsThroughCoarse : Set where
  constructor futureFactorsThroughCoarse
  field
    factor : CoarseChemicalChart → FutureBranchReadout
    law : (x : ChiralBiasState) → futureAfterStep x ≡ factor (coarseChemicalChart x)

open FutureFactorsThroughCoarse public

futureBranchDoesNotFactorThroughCoarse : FutureFactorsThroughCoarse → ⊥
futureBranchDoesNotFactorThroughCoarse F =
  futureSeedsSeparate
    (trans
      (law F leftSeed)
      (sym (law F rightSeed)))

record AsymmetricChiralDynamicsBoundary : Set where
  constructor asymmetricChiralDynamicsBoundary
  field
    lawMirrorSymmetric : Bool
    lawMirrorSymmetricIsTrue : lawMirrorSymmetric ≡ true

    realisedNonracemicBranchesExist : Bool
    realisedNonracemicBranchesExistIsTrue : realisedNonracemicBranchesExist ≡ true

    chiralityForgettingObserverPredictivelySufficient : Bool
    chiralityForgettingObserverPredictivelySufficientIsFalse :
      chiralityForgettingObserverPredictivelySufficient ≡ false

    finiteFixtureIsQuantitativeKinetics : Bool
    finiteFixtureIsQuantitativeKineticsIsFalse :
      finiteFixtureIsQuantitativeKinetics ≡ false

canonicalAsymmetricChiralDynamicsBoundary : AsymmetricChiralDynamicsBoundary
canonicalAsymmetricChiralDynamicsBoundary =
  asymmetricChiralDynamicsBoundary
    true refl
    true refl
    false refl
    false refl
