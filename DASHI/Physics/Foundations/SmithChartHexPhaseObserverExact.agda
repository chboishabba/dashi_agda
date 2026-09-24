module DASHI.Physics.Foundations.SmithChartHexPhaseObserverExact where

------------------------------------------------------------------------
-- SMITH ADMITTANCE HALF-TURN -> BASE369 HEX PHASE OBSERVER
--
-- Continuous Smith geometry:
--
--   z |-> 1/z
--   Gamma |-> -Gamma
--
-- is a half-turn in the complex reflection-coefficient plane.
--
-- Existing DASHI finite geometry:
--
--   Base369MobiusTransport.mobiusTransport
--
-- is the +3 mod-6 half-turn on HexTruth.  It flips the C2 orientation
-- polarity while preserving the C3 triadic phase quotient.
--
-- This module states the exact equivariance condition needed for a Smith
-- phase-six observer to respect that half-turn.  Under that one condition,
-- the existing Base369 C6 -> C3/C2 decomposition applies automatically.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Base369 as Base
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Physics.Foundations.SmithChartComplexReflectionExact as Smith

record SmithHexPhaseObserver
    (F : Smith.SmithComplexField) : Set₁ where
  field
    observeHex :
      Smith.C F → Base.HexTruth

    negationIsHalfTurn :
      (gamma : Smith.C F) →
      observeHex (Smith.neg F gamma)
      ≡
      Mobius.mobiusTransport (observeHex gamma)

open SmithHexPhaseObserver public

smithAdmittanceObservedAsHexHalfTurn :
  ∀ {F}
    (O : SmithHexPhaseObserver F)
    (z : Smith.C F) →
  observeHex O
    (Smith.normalizedReflection F
      (Smith.normalizedAdmittance F z))
  ≡
  Mobius.mobiusTransport
    (observeHex O
      (Smith.normalizedReflection F z))
smithAdmittanceObservedAsHexHalfTurn {F} O z =
  begin
    observeHex O
      (Smith.normalizedReflection F
        (Smith.normalizedAdmittance F z))
      ≡⟨ cong (observeHex O)
            (Smith.smithAdmittanceRotatesReflectionByHalfTurn F z) ⟩
    observeHex O
      (Smith.neg F (Smith.normalizedReflection F z))
      ≡⟨ negationIsHalfTurn O
            (Smith.normalizedReflection F z) ⟩
    Mobius.mobiusTransport
      (observeHex O (Smith.normalizedReflection F z))
  ∎

smithAdmittancePreservesTriadicPhaseObservation :
  ∀ {F}
    (O : SmithHexPhaseObserver F)
    (z : Smith.C F) →
  Mobius.hexTriadicPhase
    (observeHex O
      (Smith.normalizedReflection F
        (Smith.normalizedAdmittance F z)))
  ≡
  Mobius.hexTriadicPhase
    (observeHex O
      (Smith.normalizedReflection F z))
smithAdmittancePreservesTriadicPhaseObservation O z =
  begin
    Mobius.hexTriadicPhase
      (observeHex O
        (Smith.normalizedReflection _
          (Smith.normalizedAdmittance _ z)))
      ≡⟨ cong Mobius.hexTriadicPhase
            (smithAdmittanceObservedAsHexHalfTurn O z) ⟩
    Mobius.hexTriadicPhase
      (Mobius.mobiusTransport
        (observeHex O (Smith.normalizedReflection _ z)))
      ≡⟨ Mobius.mobiusTransport-preservesTriadicPhase
            (observeHex O (Smith.normalizedReflection _ z)) ⟩
    Mobius.hexTriadicPhase
      (observeHex O (Smith.normalizedReflection _ z))
  ∎

smithAdmittanceFlipsOrientationObservation :
  ∀ {F}
    (O : SmithHexPhaseObserver F)
    (z : Smith.C F) →
  Mobius.hexOrientationPolarity
    (observeHex O
      (Smith.normalizedReflection F
        (Smith.normalizedAdmittance F z)))
  ≡
  Mobius.flipOrientationPolarity
    (Mobius.hexOrientationPolarity
      (observeHex O
        (Smith.normalizedReflection F z)))
smithAdmittanceFlipsOrientationObservation O z =
  begin
    Mobius.hexOrientationPolarity
      (observeHex O
        (Smith.normalizedReflection _
          (Smith.normalizedAdmittance _ z)))
      ≡⟨ cong Mobius.hexOrientationPolarity
            (smithAdmittanceObservedAsHexHalfTurn O z) ⟩
    Mobius.hexOrientationPolarity
      (Mobius.mobiusTransport
        (observeHex O (Smith.normalizedReflection _ z)))
      ≡⟨ Mobius.mobiusTransport-flipsOrientationPolarity
            (observeHex O (Smith.normalizedReflection _ z)) ⟩
    Mobius.flipOrientationPolarity
      (Mobius.hexOrientationPolarity
        (observeHex O (Smith.normalizedReflection _ z)))
  ∎

record SmithHexCrossPollinationBoundary : Set where
  constructor smith-hex-cross-pollination-boundary
  field
    smithAdmittanceIsContinuousHalfTurn : Bool
    base369HexTransportIsFiniteHalfTurn : Bool
    equivariantObserverCompilerOwned : Bool
    triadicPhaseQuotientPreserved : Bool
    orientationPolarityFlipped : Bool

    smithHexObserverInhabitedHere : Bool
    smithPhaseIdentifiedWithModularJPhase : Bool
    smithAdmittanceIdentifiedWithModularT : Bool
    smithAdmittanceIdentifiedWithModularReflection : Bool

canonicalSmithHexCrossPollinationBoundary :
  SmithHexCrossPollinationBoundary
canonicalSmithHexCrossPollinationBoundary =
  smith-hex-cross-pollination-boundary
    true true true true true
    false false false false
