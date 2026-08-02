module DASHI.Physics.Closure.NSTriadKNBernsteinDirectionAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Daniel Raban.
-- Title: "Math 247A Lecture 20 Notes".
-- Venue/year: UCLA Math 247A lecture notes, 24 February 2020.
-- DOI: none; these are course lecture notes rather than a journal article.
-- Uses: Theorem 1.1(4)--(5), including annular Bernstein equivalence,
-- low-pass derivative upper bounds, and high-frequency Sobolev-tail decay.
-- Relationship: separates the three logically different Bernstein directions
-- so a low-frequency derivative cost cannot be silently rewritten as decay.
--
-- Author: Terence Tao.
-- Title: "Lecture Notes 6 for 247B: Paradifferential calculus,
-- fractional chain and Leibnitz rules".
-- Venue/year: UCLA Math 247B Fourier Analysis lecture notes, Winter 2007.
-- DOI: none; these are course lecture notes rather than a journal article.
-- Uses: high-high, high-low, and low-high frequency placement in the
-- paradifferential calculus.
-- Relationship: contextual provenance only; no source-specific constant is
-- transferred to the discrete orbit-shell carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

data FrequencySupport : Set where
  annularSupport lowPassSupport highPassSupport : FrequencySupport

data PowerDirection : Set where
  positiveDerivativeCost negativeTailDecay : PowerDirection

record RationalPower : Set where
  constructor power
  field
    direction : PowerDirection
    numeratorMagnitude : Nat
    denominator : Nat

open RationalPower public

representativeSobolevNumerator representativeSobolevDenominator : Nat
representativeSobolevNumerator = 8
representativeSobolevDenominator = 3

annularDerivativePower lowPassDerivativePower highPassTailPower :
  RationalPower
annularDerivativePower = power positiveDerivativeCost 8 3
lowPassDerivativePower = power positiveDerivativeCost 8 3
highPassTailPower = power negativeTailDecay 8 3

record BernsteinDirectionReceipt : Set where
  constructor receipt
  field
    representativeSIsEightThirds :
      representativeSobolevNumerator ≡ 8
    representativeDenominatorIsThree :
      representativeSobolevDenominator ≡ 3
    annularMagnitudeIsEight :
      numeratorMagnitude annularDerivativePower ≡ 8
    lowPassMagnitudeIsEight :
      numeratorMagnitude lowPassDerivativePower ≡ 8
    highPassMagnitudeIsEight :
      numeratorMagnitude highPassTailPower ≡ 8
    annularCostsDerivatives :
      direction annularDerivativePower ≡ positiveDerivativeCost
    lowPassCostsDerivatives :
      direction lowPassDerivativePower ≡ positiveDerivativeCost
    highPassSuppliesTailDecay :
      direction highPassTailPower ≡ negativeTailDecay

open BernsteinDirectionReceipt public

bernsteinDirectionReceipt : BernsteinDirectionReceipt
bernsteinDirectionReceipt =
  receipt refl refl refl refl refl refl refl refl

record BernsteinDirectionCarrier
    {f s e : Level} : Set (lsuc (f ⊔ s ⊔ e)) where
  field
    Function : Set f
    Scalar : Set s
    Exponent : Set e

    annularProjection : Exponent → Function → Function
    lowPassProjection : Exponent → Function → Function
    highPassProjection : Exponent → Function → Function
    derivative : Exponent → Function → Function
    norm : Function → Scalar

    bernsteinAnnularDerivativeEquivalence : Set s
    bernsteinLowFrequencyDerivativeUpperBound : Set s
    bernsteinHighFrequencyTailDecayFromSobolev : Set s

    lowFrequencyDecayRequiresAdditionalSobolevInput : Set s
    noReverseLowPassDecayFromBernsteinAlone : Set s

    derivativeOwnerRecordedPerFrozenLeg : Set s
    highHighToLowUsesCancellationOrSobolevInput : Set s
    directionCheckedBeforeExponentAssembly : Set s

open BernsteinDirectionCarrier public

bernsteinDirectionSurfaceRepresented : Bool
bernsteinDirectionSurfaceRepresented = true

bernsteinDirectionSurfaceRepresentedIsTrue :
  bernsteinDirectionSurfaceRepresented ≡ true
bernsteinDirectionSurfaceRepresentedIsTrue = refl

bernsteinAloneSuppliesLowFrequencyDecay : Bool
bernsteinAloneSuppliesLowFrequencyDecay = false

bernsteinAloneSuppliesLowFrequencyDecayIsFalse :
  bernsteinAloneSuppliesLowFrequencyDecay ≡ false
bernsteinAloneSuppliesLowFrequencyDecayIsFalse = refl

highHighToLowNeedsCancellationOrSobolevInput : Bool
highHighToLowNeedsCancellationOrSobolevInput = true

highHighToLowNeedsCancellationOrSobolevInputIsTrue :
  highHighToLowNeedsCancellationOrSobolevInput ≡ true
highHighToLowNeedsCancellationOrSobolevInputIsTrue = refl
