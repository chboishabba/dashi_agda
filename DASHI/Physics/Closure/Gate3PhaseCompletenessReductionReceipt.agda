module DASHI.Physics.Closure.Gate3PhaseCompletenessReductionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MonsterIrrepCarrierDecompositionReceipt as Monster
import DASHI.Physics.Closure.SSPSevenSevenOneFrameDecompositionReceipt as Frame

------------------------------------------------------------------------
-- Gate 3 phase-completeness reduction.
--
-- This receipt isolates the useful Gate 3 content of the Monster/T7/zeta7
-- lane: phase data is necessary for the inert/complex character sector, but
-- it is not a uniform frame lower-bound proof.  The exact remaining targets
-- are A_split > 0, A_inert > 0, A_71 > 0, uniform cutoff lift, and then the
-- Mosco/no-spectral-pollution bridge.  The latest toy-model attempt also
-- records that purely one-dimensional, position-orthogonal Gram models cannot
-- distinguish phase-blind from phase-complete dictionaries; the failure mode
-- requires cross-sector spatial overlap in the full R^3 Archimedean image.

data Gate3PhaseCompletenessReductionStatus : Set where
  phaseCompletenessNecessary_uniformLowerBoundStillOpen :
    Gate3PhaseCompletenessReductionStatus

data Gate3PhaseReductionClause : Set where
  phaseBlindLosesInertOrComplexCharacterResolution :
    Gate3PhaseReductionClause

  mirrorB7RestoresPhaseCharacterResolution :
    Gate3PhaseReductionClause

  phaseCompletenessNecessaryNotSufficient :
    Gate3PhaseReductionClause

  lowerBoundRequiresSplitInertAndObserverFactors :
    Gate3PhaseReductionClause

  oneDimensionalToyModelCannotSeparatePhaseSectors :
    Gate3PhaseReductionClause

  threeDimensionalArchimedeanOverlapRequired :
    Gate3PhaseReductionClause

canonicalGate3PhaseReductionClauses :
  List Gate3PhaseReductionClause
canonicalGate3PhaseReductionClauses =
  phaseBlindLosesInertOrComplexCharacterResolution
  ∷ mirrorB7RestoresPhaseCharacterResolution
  ∷ phaseCompletenessNecessaryNotSufficient
  ∷ lowerBoundRequiresSplitInertAndObserverFactors
  ∷ oneDimensionalToyModelCannotSeparatePhaseSectors
  ∷ threeDimensionalArchimedeanOverlapRequired
  ∷ []

data Gate3PhaseOpenLemma : Set where
  proveASplitPositive :
    Gate3PhaseOpenLemma

  proveAInertPositive :
    Gate3PhaseOpenLemma

  proveASeventyOnePositive :
    Gate3PhaseOpenLemma

  proveUniformCutoffLowerBound :
    Gate3PhaseOpenLemma

  proveMoscoNoSpectralPollutionLift :
    Gate3PhaseOpenLemma

canonicalGate3PhaseOpenLemmas :
  List Gate3PhaseOpenLemma
canonicalGate3PhaseOpenLemmas =
  proveASplitPositive
  ∷ proveAInertPositive
  ∷ proveASeventyOnePositive
  ∷ proveUniformCutoffLowerBound
  ∷ proveMoscoNoSpectralPollutionLift
  ∷ []

data Gate3PhasePromotion : Set where

gate3PhasePromotionImpossibleHere :
  Gate3PhasePromotion →
  ⊥
gate3PhasePromotionImpossibleHere ()

phaseCompletenessReductionStatement :
  String
phaseCompletenessReductionStatement =
  "Phase-complete MirrorB7 data is necessary for the inert/complex character sector, but Gate 3 still requires A_split > 0, A_inert > 0, A_71 > 0, uniform cutoff lower bound, and Mosco/no-pollution."

phaseBlindFailureReductionStatement :
  String
phaseBlindFailureReductionStatement =
  "The phase-blind dictionary is recorded as losing inert/complex phase resolution only when cross-sector spatial overlap is present; a 1D position-orthogonal toy Gram model block-diagonalises and cannot witness the failure."

gate3ToyModelStatement :
  String
gate3ToyModelStatement =
  "Attempted 1D Gram models make blind and complete sectors identical when sectors are orthogonal by position.  Gate3 phase-completeness must therefore be tested in the physical 3D Hecke/SSP Archimedean image."

record Gate3PhaseCompletenessReductionReceipt : Setω where
  field
    status :
      Gate3PhaseCompletenessReductionStatus

    statusIsCanonical :
      status ≡ phaseCompletenessNecessary_uniformLowerBoundStillOpen

    monsterReceipt :
      Monster.MonsterIrrepCarrierDecompositionReceipt

    monsterGate3FrameStillOpen :
      Monster.gate3FrameBoundProvedHere monsterReceipt ≡ false

    monsterGate3NotPromoted :
      Monster.gate3Promoted monsterReceipt ≡ false

    frameReceipt :
      Frame.SSPSevenSevenOneFrameDecompositionReceipt

    framePhaseBlindFails :
      Frame.phaseBlindDictionaryFrameFails frameReceipt ≡ true

    framePhaseCompletePotential :
      Frame.phaseCompleteDictionaryPotentiallyValid frameReceipt ≡ true

    frameUniformLowerBoundStillOpen :
      Frame.uniformLowerBoundProved frameReceipt ≡ false

    frameGate3ClosedFalse :
      Frame.gate3Closed frameReceipt ≡ false

    reductionClauses :
      List Gate3PhaseReductionClause

    reductionClausesAreCanonical :
      reductionClauses ≡ canonicalGate3PhaseReductionClauses

    openLemmas :
      List Gate3PhaseOpenLemma

    openLemmasAreCanonical :
      openLemmas ≡ canonicalGate3PhaseOpenLemmas

    phaseCompletenessNecessary :
      Bool

    phaseCompletenessNecessaryIsTrue :
      phaseCompletenessNecessary ≡ true

    phaseCompletenessSufficientForGate3 :
      Bool

    phaseCompletenessSufficientForGate3IsFalse :
      phaseCompletenessSufficientForGate3 ≡ false

    toyModel1DBlindAndCompleteIdentical :
      Bool

    toyModel1DBlindAndCompleteIdenticalIsTrue :
      toyModel1DBlindAndCompleteIdentical ≡ true

    toyModel3DRequiredForCrossSectorOverlap :
      Bool

    toyModel3DRequiredForCrossSectorOverlapIsTrue :
      toyModel3DRequiredForCrossSectorOverlap ≡ true

    aSplitProvedPositive :
      Bool

    aSplitProvedPositiveIsFalse :
      aSplitProvedPositive ≡ false

    aInertProvedPositive :
      Bool

    aInertProvedPositiveIsFalse :
      aInertProvedPositive ≡ false

    aSeventyOneProvedPositive :
      Bool

    aSeventyOneProvedPositiveIsFalse :
      aSeventyOneProvedPositive ≡ false

    uniformCutoffLowerBoundProved :
      Bool

    uniformCutoffLowerBoundProvedIsFalse :
      uniformCutoffLowerBoundProved ≡ false

    gate3SpectralGapProved :
      Bool

    gate3SpectralGapProvedIsFalse :
      gate3SpectralGapProved ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List Gate3PhasePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3PhasePromotion →
      ⊥

    reductionText :
      String

    reductionTextIsCanonical :
      reductionText ≡ phaseCompletenessReductionStatement

    failureText :
      String

    failureTextIsCanonical :
      failureText ≡ phaseBlindFailureReductionStatement

    toyModelText :
      String

    toyModelTextIsCanonical :
      toyModelText ≡ gate3ToyModelStatement

open Gate3PhaseCompletenessReductionReceipt public

canonicalGate3PhaseCompletenessReductionReceipt :
  Gate3PhaseCompletenessReductionReceipt
canonicalGate3PhaseCompletenessReductionReceipt =
  record
    { status =
        phaseCompletenessNecessary_uniformLowerBoundStillOpen
    ; statusIsCanonical =
        refl
    ; monsterReceipt =
        Monster.canonicalMonsterIrrepCarrierDecompositionReceipt
    ; monsterGate3FrameStillOpen =
        refl
    ; monsterGate3NotPromoted =
        refl
    ; frameReceipt =
        Frame.canonicalSSPSevenSevenOneFrameDecompositionReceipt
    ; framePhaseBlindFails =
        refl
    ; framePhaseCompletePotential =
        refl
    ; frameUniformLowerBoundStillOpen =
        refl
    ; frameGate3ClosedFalse =
        refl
    ; reductionClauses =
        canonicalGate3PhaseReductionClauses
    ; reductionClausesAreCanonical =
        refl
    ; openLemmas =
        canonicalGate3PhaseOpenLemmas
    ; openLemmasAreCanonical =
        refl
    ; phaseCompletenessNecessary =
        true
    ; phaseCompletenessNecessaryIsTrue =
        refl
    ; phaseCompletenessSufficientForGate3 =
        false
    ; phaseCompletenessSufficientForGate3IsFalse =
        refl
    ; toyModel1DBlindAndCompleteIdentical =
        true
    ; toyModel1DBlindAndCompleteIdenticalIsTrue =
        refl
    ; toyModel3DRequiredForCrossSectorOverlap =
        true
    ; toyModel3DRequiredForCrossSectorOverlapIsTrue =
        refl
    ; aSplitProvedPositive =
        false
    ; aSplitProvedPositiveIsFalse =
        refl
    ; aInertProvedPositive =
        false
    ; aInertProvedPositiveIsFalse =
        refl
    ; aSeventyOneProvedPositive =
        false
    ; aSeventyOneProvedPositiveIsFalse =
        refl
    ; uniformCutoffLowerBoundProved =
        false
    ; uniformCutoffLowerBoundProvedIsFalse =
        refl
    ; gate3SpectralGapProved =
        false
    ; gate3SpectralGapProvedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3PhasePromotionImpossibleHere
    ; reductionText =
        phaseCompletenessReductionStatement
    ; reductionTextIsCanonical =
        refl
    ; failureText =
        phaseBlindFailureReductionStatement
    ; failureTextIsCanonical =
        refl
    ; toyModelText =
        gate3ToyModelStatement
    ; toyModelTextIsCanonical =
        refl
    }

gate3PhaseReductionKeepsGate3Open :
  gate3SpectralGapProved canonicalGate3PhaseCompletenessReductionReceipt
  ≡
  false
gate3PhaseReductionKeepsGate3Open =
  refl

gate3PhaseReductionIsNecessaryOnly :
  phaseCompletenessSufficientForGate3
    canonicalGate3PhaseCompletenessReductionReceipt
  ≡
  false
gate3PhaseReductionIsNecessaryOnly =
  refl

gate3ToyModelForces3DEmbeddingObligation :
  toyModel3DRequiredForCrossSectorOverlap
    canonicalGate3PhaseCompletenessReductionReceipt
  ≡
  true
gate3ToyModelForces3DEmbeddingObligation =
  refl
