module DASHI.Physics.Closure.NSTriadKNQuarticSignedNearFarDecomposition where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: Chapter 2, Bony decomposition and dyadic interaction classes.
-- Relationship: adapts the paraproduct taxonomy to the exact signed periodic
-- triad fibres.  The seven-class equality is a DASHI-specific proof target.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_)

data SignedCubicClass : Set where
  near lowHigh highLow farLow farHigh transition residualChartSwitch :
    SignedCubicClass

record ExactSignedNearFarDecomposition {c s : Level} :
    Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    fullCubicMagnitude : Cutoff → State → Nat
    classMagnitude :
      SignedCubicClass → Cutoff → State → Nat

    literalSevenClassPartition : ∀ N state →
      fullCubicMagnitude N state
      ≡
      classMagnitude near N state
      + (classMagnitude lowHigh N state
      + (classMagnitude highLow N state
      + (classMagnitude farLow N state
      + (classMagnitude farHigh N state
      + (classMagnitude transition N state
      + classMagnitude residualChartSwitch N state)))))

open ExactSignedNearFarDecomposition public

record QuantitativeNearFarBounds
    {c s : Level}
    (D : ExactSignedNearFarDecomposition {c} {s}) :
    Set (lsuc (c ⊔ s)) where
  field
    dissipation controlledRemainder :
      Cutoff D → State D → Nat

    nearNumerator nearDenominator : Nat
    farLowNumerator farLowDenominator : Nat
    farHighNumerator farHighDenominator : Nat
    transitionConstant residualConstant : Nat

    nearBound : ∀ N state →
      nearDenominator *
        classMagnitude D near N state
      ≤
      nearNumerator * dissipation N state
      + nearDenominator * controlledRemainder N state

    farLowCommutatorGainsRadius : ∀ N state →
      farLowDenominator *
        classMagnitude D farLow N state
      ≤ farLowNumerator * dissipation N state

    farHighSobolevTailGainsRadius : ∀ N state →
      farHighDenominator *
        classMagnitude D farHigh N state
      ≤ farHighNumerator * dissipation N state

    transitionBound : ∀ N state →
      classMagnitude D transition N state
      ≤ transitionConstant * controlledRemainder N state

    residualChartSwitchBound : ∀ N state →
      classMagnitude D residualChartSwitch N state
      ≤ residualConstant * controlledRemainder N state

open QuantitativeNearFarBounds public

exactSevenClassTargetImplemented : Bool
exactSevenClassTargetImplemented = true

exactSevenClassTargetImplementedIsTrue :
  exactSevenClassTargetImplemented ≡ true
exactSevenClassTargetImplementedIsTrue = refl

literalSignedSevenClassEqualityClosed : Bool
literalSignedSevenClassEqualityClosed = false

literalSignedSevenClassEqualityClosedIsFalse :
  literalSignedSevenClassEqualityClosed ≡ false
literalSignedSevenClassEqualityClosedIsFalse = refl
