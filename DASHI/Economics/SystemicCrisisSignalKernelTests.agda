module DASHI.Economics.SystemicCrisisSignalKernelTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)
open import DASHI.Economics.SystemicCrisisSignalKernel

normalObservation : CrisisObservation
normalObservation = observation neg neg neg neg neg neg neg

fragilityObservation : CrisisObservation
fragilityObservation = observation pos pos zer neg zer neg neg

proximityObservation : CrisisObservation
proximityObservation = observation pos zer pos pos zer neg neg

activeObservation : CrisisObservation
activeObservation = observation pos pos pos pos pos neg neg

recoveryObservation : CrisisObservation
recoveryObservation = observation zer neg zer neg neg pos pos

normalClassifies : instantPhase normalObservation ≡ normalPhase
normalClassifies = refl

fragilityClassifies : instantPhase fragilityObservation ≡ fragilityPhase
fragilityClassifies = refl

proximityClassifies : instantPhase proximityObservation ≡ proximityPhase
proximityClassifies = refl

activeClassifies : instantPhase activeObservation ≡ activePhase
activeClassifies = refl

activePersistsWithoutRecovery :
  stepPhase activePhase normalObservation ≡ activePhase
activePersistsWithoutRecovery = refl

activeEntersAbatingOnMechanicalRecovery :
  stepPhase activePhase recoveryObservation ≡ abatingPhase
activeEntersAbatingOnMechanicalRecovery = refl

abatingReturnsToNormal :
  stepPhase abatingPhase normalObservation ≡ normalPhase
abatingReturnsToNormal = refl

activePosturePreservesLiquidity :
  posture activePhase ≡ preserveLiquidityPosture
activePosturePreservesLiquidity = refl

singleTickerStoryCannotPromoteNormalPlumbing :
  classifyWithNarrative
    normalObservation
    (narrative pos true true)
  ≡ normalPhase
singleTickerStoryCannotPromoteNormalPlumbing = refl

oppositeStoriesSameMechanismPhase :
  classifyWithNarrative
    proximityObservation
    (narrative pos true true)
  ≡
  classifyWithNarrative
    proximityObservation
    (narrative neg false false)
oppositeStoriesSameMechanismPhase = refl
