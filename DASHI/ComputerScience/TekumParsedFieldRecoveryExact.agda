module DASHI.ComputerScience.TekumParsedFieldRecoveryExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as ℤ using (ℤ; _+_; _-_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; -_; _+_; _*_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Data.Vec.Properties using (reverse-injective)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFractionInjectiveExact as FractionInjective
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumParsedExponentInjectiveExact as ExponentInjective
import DASHI.ComputerScience.TekumRegimeChainExact as RegimeChain
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSignificandRangeExact as Significand
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale

------------------------------------------------------------------------
-- PARSED FIELD RECOVERY FROM THE LITERAL POSITIVE MAGNITUDE
--
-- This owner is deliberately downstream of the same-object rational
-- factorisation and the arbitrary exponent-band separation.  It contains no
-- second numerical semantics: every recovered field is the field carried by
-- Source.ParsedPayload itself.
------------------------------------------------------------------------

module RingZ = NR IntRS.ring
open RingZ using (_⊕_; ⊝_; _⊜_)

cancelRightAdd :
  (x y b : ℤ) → x ℤ.+ b ≡ y ℤ.+ b → x ≡ y
cancelRightAdd x y b eq =
  trans
    (sym (subtractRight x b))
    (trans
      (cong (λ z → z ℤ.- b) eq)
      (subtractRight y b))
  where
  subtractRight : (a c : ℤ) → (a ℤ.+ c) ℤ.- c ≡ a
  subtractRight a c =
    RingZ.solve 2
      (λ a c → (((a ⊕ c) ⊕ (⊝ c)) ⊜ a))
      refl a c

-- Equality of the positive magnitudes first identifies the integer exponent by
-- the arbitrary-gap band theorem; the source regime table then identifies the
-- unique regime block containing that exponent.
equalMagnitudeForceRegime :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  r ≡ s
equalMagnitudeForceRegime p q magnitudeEq =
  RegimeChain.equalParsedExponentForcesRegime p q
    (ExponentInjective.equalParsedMagnitudesForceExponent p q magnitudeEq)

regimeBiasInteger : Regime.RegimeCode → ℤ
regimeBiasInteger r = Exact.intCodeToInteger (Regime.bias r)

-- Once the regime is fixed, equal decoded exponents cancel the common source
-- bias.  Balanced positional injectivity then recovers the literal exponent
-- trits (in the parser's LST orientation).
equalExponentSameRegimeForceExponentField :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q →
  Source.exponentLST p ≡ Source.exponentLST q
equalExponentSameRegimeForceExponentField {r = r} p q exponentEq =
  Positional.toIntegerInjective fieldIntegerEq
  where
  fieldPlusBiasEq :
    BT.toInteger (BT.eval (Source.exponentLST p)) ℤ.+ regimeBiasInteger r
    ≡
    BT.toInteger (BT.eval (Source.exponentLST q)) ℤ.+ regimeBiasInteger r
  fieldPlusBiasEq =
    trans
      (sym (Source.exponentIntCodeInteger p))
      (trans exponentEq (Source.exponentIntCodeInteger q))

  fieldIntegerEq :
    BT.toInteger (BT.eval (Source.exponentLST p))
    ≡ BT.toInteger (BT.eval (Source.exponentLST q))
  fieldIntegerEq =
    cancelRightAdd
      (BT.toInteger (BT.eval (Source.exponentLST p)))
      (BT.toInteger (BT.eval (Source.exponentLST q)))
      (regimeBiasInteger r)
      fieldPlusBiasEq

-- Equal magnitude at an equal exponent leaves only the significand.  We cancel
-- the common strictly-positive power-of-three scale using ordered-field
-- cancellation, avoiding any quotient normalization argument.
equalMagnitudeSameRegimeForceSignificand :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  Significand.significand (Source.fractionLST p)
  ≡ Significand.significand (Source.fractionLST q)
equalMagnitudeSameRegimeForceSignificand p q magnitudeEq =
  ℚP.≤-antisym
    (ℚP.*-cancelʳ-≤-pos scale (ℚP.≤-reflexive productEq))
    (ℚP.*-cancelʳ-≤-pos scale (ℚP.≤-reflexive (sym productEq)))
  where
  exponentEq =
    ExponentInjective.equalParsedMagnitudesForceExponent p q magnitudeEq

  scale : ℚ
  scale = Scale.triadicScale (Factor.sourceExponentInteger p)

  instance
    scalePositive : Positive scale
    scalePositive = positive (Scale.triadicScalePositive (Factor.sourceExponentInteger p))

  productEq :
    Significand.significand (Source.fractionLST p) ℚ.* scale
    ≡ Significand.significand (Source.fractionLST q) ℚ.* scale
  productEq =
    trans
      (sym (Parsed.parsedMagnitudeIsSourceFormula p))
      (trans
        magnitudeEq
        (trans
          (Parsed.parsedMagnitudeIsSourceFormula q)
          (cong
            (λ e → Significand.significand (Source.fractionLST q) ℚ.*
                   Scale.triadicScale e)
            (sym exponentEq))))

cancelOne : (x : ℚ) → (1ℚ ℚ.+ x) ℚ.+ (ℚ.- 1ℚ) ≡ x
cancelOne = solve-∀

-- The significand is literally 1+f.  Cancelling one recovers equality of the
-- canonical fractions, and the already-paid fixed-width rational injectivity
-- recovers the exact fraction trits.
equalMagnitudeSameRegimeForceFraction :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  Source.fractionLST p ≡ Source.fractionLST q
equalMagnitudeSameRegimeForceFraction p q magnitudeEq =
  FractionInjective.canonicalFractionInjective fractionEq
  where
  significandEq = equalMagnitudeSameRegimeForceSignificand p q magnitudeEq

  shifted :
    (Significand.significand (Source.fractionLST p) ℚ.+ (ℚ.- 1ℚ))
    ≡
    (Significand.significand (Source.fractionLST q) ℚ.+ (ℚ.- 1ℚ))
  shifted = cong (λ z → z ℚ.+ (ℚ.- 1ℚ)) significandEq

  fractionEq :
    Fraction.canonicalFraction (Source.fractionLST p)
    ≡ Fraction.canonicalFraction (Source.fractionLST q)
  fractionEq =
    trans
      (sym (cancelOne (Fraction.canonicalFraction (Source.fractionLST p))))
      (trans shifted
        (cancelOne (Fraction.canonicalFraction (Source.fractionLST q))))

-- The parser stores those numerical fields in MSB order; reverse is injective,
-- so numerical-field recovery also recovers the literal source field vectors.
equalExponentSameRegimeForceExponentMSB :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Factor.sourceExponentInteger p ≡ Factor.sourceExponentInteger q →
  Source.exponentMSB p ≡ Source.exponentMSB q
equalExponentSameRegimeForceExponentMSB p q exponentEq =
  reverse-injective (equalExponentSameRegimeForceExponentField p q exponentEq)

equalMagnitudeSameRegimeForceFractionMSB :
  ∀ {extra r payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra r payload₂) →
  Parsed.parsedMagnitude p ≡ Parsed.parsedMagnitude q →
  Source.fractionMSB p ≡ Source.fractionMSB q
equalMagnitudeSameRegimeForceFractionMSB p q magnitudeEq =
  reverse-injective (equalMagnitudeSameRegimeForceFraction p q magnitudeEq)
