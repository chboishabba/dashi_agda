module DASHI.Moonshine.JInvariantSmithChartMobiusMatrixBridgeExact where

------------------------------------------------------------------------
-- SMITH MOBIUS MATRIX -> C6/C3 OBSERVER BRIDGE
--
-- Continuous lane:
--
--   z --A--> 1/z --Gamma--> -Gamma
--
-- where
--
--   A = [0 1; 1 0]
--   Gamma = [1 -1; 1 1].
--
-- Finite observer lane:
--
--   C6 --(+3 mod 6)--> C6 --forget orientation--> C3.
--
-- This module composes the genuine Smith Möbius matrix owner with the existing
-- finite Smith observer theorem.  It does not identify Smith Gamma, the
-- engineering imaginary unit j_EE, or the finite half-turn with modular j,
-- modular T, or modular reflection.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

import Base369 as Base
import DASHI.Foundations.Base369MobiusTransport as Finite
import DASHI.Physics.Foundations.SmithChartComplexReflectionExact as Smith
import DASHI.Physics.Foundations.SmithChartMobiusMatrixExact as Matrix
import DASHI.Physics.Foundations.SmithChartHexPhaseObserverExact as Hex
import DASHI.Moonshine.JInvariantSmithChartActionSeparationExact as Separation

record SmithMobiusHexBundle
    (F : Smith.SmithComplexField) : Set₁ where
  field
    matrixLaws :
      Matrix.SmithMobiusMatrixLaws F

    hexObserver :
      Hex.SmithHexPhaseObserver F

open SmithMobiusHexBundle public

------------------------------------------------------------------------
-- Exact C6 commuting square from the Möbius admittance matrix.
------------------------------------------------------------------------

smithAdmittanceMatrixObservedAsHexHalfTurn :
  ∀ {F} →
  (B : SmithMobiusHexBundle F) →
  (z : Smith.C F) →
  Hex.observeHex (hexObserver B)
    (Smith.normalizedReflection F
      (Matrix.mobiusEvaluate F
        (Matrix.normalizedAdmittanceMatrix F)
        z))
  ≡
  Finite.mobiusTransport
    (Hex.observeHex (hexObserver B)
      (Smith.normalizedReflection F z))
smithAdmittanceMatrixObservedAsHexHalfTurn {F} B z =
  trans
    (cong
      (λ input →
        Hex.observeHex (hexObserver B)
          (Smith.normalizedReflection F input))
      (Matrix.normalizedAdmittanceIsMobius
        (matrixLaws B) z))
    (Hex.smithAdmittanceObservedAsHexHalfTurn
      (hexObserver B) z)

------------------------------------------------------------------------
-- The C3 orientation-forgetting quotient erases that nontrivial C6 action.
------------------------------------------------------------------------

smithAdmittanceMatrixInvisibleAtC3 :
  ∀ {F} →
  (B : SmithMobiusHexBundle F) →
  (z : Smith.C F) →
  Finite.hexTriadicPhase
    (Hex.observeHex (hexObserver B)
      (Smith.normalizedReflection F
        (Matrix.mobiusEvaluate F
          (Matrix.normalizedAdmittanceMatrix F)
          z)))
  ≡
  Finite.hexTriadicPhase
    (Hex.observeHex (hexObserver B)
      (Smith.normalizedReflection F z))
smithAdmittanceMatrixInvisibleAtC3 {F} B z =
  trans
    (cong Finite.hexTriadicPhase
      (smithAdmittanceMatrixObservedAsHexHalfTurn B z))
    (Finite.mobiusTransport-preservesTriadicPhase
      (Hex.observeHex (hexObserver B)
        (Smith.normalizedReflection F z)))

------------------------------------------------------------------------
-- Yet the C2 orientation coordinate flips.
------------------------------------------------------------------------

smithAdmittanceMatrixFlipsC2Orientation :
  ∀ {F} →
  (B : SmithMobiusHexBundle F) →
  (z : Smith.C F) →
  Finite.hexOrientationPolarity
    (Hex.observeHex (hexObserver B)
      (Smith.normalizedReflection F
        (Matrix.mobiusEvaluate F
          (Matrix.normalizedAdmittanceMatrix F)
          z)))
  ≡
  Finite.flipOrientationPolarity
    (Finite.hexOrientationPolarity
      (Hex.observeHex (hexObserver B)
        (Smith.normalizedReflection F z)))
smithAdmittanceMatrixFlipsC2Orientation {F} B z =
  trans
    (cong Finite.hexOrientationPolarity
      (smithAdmittanceMatrixObservedAsHexHalfTurn B z))
    (Finite.mobiusTransport-flipsOrientationPolarity
      (Hex.observeHex (hexObserver B)
        (Smith.normalizedReflection F z)))

------------------------------------------------------------------------
-- Action separation is inherited from the already-proved finite theorem.
------------------------------------------------------------------------

smithMobiusHalfTurnNotModularT :
  ¬ Separation.HalfTurnIsPhaseIdentity
smithMobiusHalfTurnNotModularT =
  Separation.smithHalfTurnIsNotModularTPhaseIdentity

smithMobiusHalfTurnNotModularReflection :
  ¬ Separation.HalfTurnIsModularReflection
smithMobiusHalfTurnNotModularReflection =
  Separation.smithHalfTurnIsNotModularReflection

record SmithMobiusMatrixBridgeBoundary : Set where
  constructor smith-mobius-matrix-bridge-boundary
  field
    continuousAdmittanceMatrixOwned : Bool
    continuousGammaMatrixOwned : Bool
    matrixToC6CommutingSquareOwned : Bool
    c3QuotientErasesMatrixHalfTurn : Bool
    c2OrientationFlipOwned : Bool
    halfTurnDistinctFromModularT : Bool
    halfTurnDistinctFromModularReflection : Bool

    concreteSmithMatrixHexBundleInhabitedHere : Bool
    smithGammaIdentifiedWithModularJ : Bool
    smithMobiusActionIdentifiedWithModularAction : Bool

canonicalSmithMobiusMatrixBridgeBoundary :
  SmithMobiusMatrixBridgeBoundary
canonicalSmithMobiusMatrixBridgeBoundary =
  smith-mobius-matrix-bridge-boundary
    true true true true true true true
    false false false
