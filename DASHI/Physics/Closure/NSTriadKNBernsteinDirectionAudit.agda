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
import Data.Integer.Base as Int

data FrequencySupport : Set where
  annularSupport lowPassSupport highPassSupport : FrequencySupport

data PowerDirection : Set where
  positiveDerivativeCost negativeTailDecay : PowerDirection

record RationalPower : Set where
  constructor power
  field
    numerator : Int.ℤ
    denominator : Nat

open RationalPower public

representativeSobolevNumerator representativeSobolevDenominator : Nat
representativeSobolevNumerator = 8
representativeSobolevDenominator = 3

annularDerivativePower lowPassDerivativePower highPassTailPower :
  RationalPower
annularDerivativePower = power (Int.+ 8) 3
lowPassDerivativePower = power (Int.+ 8) 3
highPassTailPower = power (Int.-[1+ 7 ]) 3

annularDirection lowPassDirection highPassDirection : PowerDirection
annularDirection = positiveDerivativeCost
lowPassDirection = positiveDerivativeCost
highPassDirection = negativeTailDecay

record BernsteinDirectionReceipt : Set where
  constructor receipt
  field
    representativeSIsEightThirds :
      representativeSobolevNumerator ≡ 8
    representativeDenominatorIsThree :
      representativeSobolevDenominator ≡ 3
    annularNumeratorPositiveEight :
      numerator annularDerivativePower ≡ Int.+ 8
    lowPassNumeratorPositiveEight :
      numerator lowPassDerivativePower ≡ Int.+ 8
    highPassNumeratorNegativeEight :
      numerator highPassTailPower ≡ Int.-[1+ 7 ]
    annularCostsDerivatives :
      annularDirection ≡ positiveDerivativeCost
    lowPassCostsDerivatives :
      lowPassDirection ≡ positiveDerivativeCost
    highPassSuppliesTailDecay :
      highPassDirection ≡ negativeTailDecay

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
