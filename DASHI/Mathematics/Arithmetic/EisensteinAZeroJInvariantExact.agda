module DASHI.Mathematics.Arithmetic.EisensteinAZeroJInvariantExact where

------------------------------------------------------------------------
-- SHORT-WEIERSTRASS j-EXPRESSION: A=0 SPECIALISATION
--
-- This is a DASHI repository extension over the already-owned exact
-- ShortWeierstrassCurve carrier.  No new external source is acquired here.
-- The formula is kept as a local exact expression and theorem surface; this
-- owner does not turn its value into CM/Hecke/elliptic-L authority.
--
--   J(A,B) = 1728 * 4 A^3 / (4 A^3 + 27 B^2)
--
-- The existing curve carrier requires
--
--   -16 * (4 A^3 + 27 B^2) != 0,
--
-- so the denominator is nonzero.  On the A=0 subfamily the numerator is zero,
-- hence this exact short-form expression is zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+0; +[1+_]; -[1+_])
open import Data.Nat.Coprimality as Coprime using ()
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; mkℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Binary.PropositionalEquality as Eq

import DASHI.Interop.Round11MachinCrossProverRecognitionExact as Attribution
import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic

------------------------------------------------------------------------
-- 1. Total rational reciprocal/division, following an existing repo pattern.
------------------------------------------------------------------------

invℚ : ℚ → ℚ
invℚ (mkℚ +0 d prf) = 0ℚ
invℚ (mkℚ +[1+ n ] d prf) = mkℚ +[1+ d ] n (Coprime.sym prf)
invℚ (mkℚ -[1+ n ] d prf) = mkℚ -[1+ d ] n (Coprime.sym prf)

_÷q_ : ℚ → ℚ → ℚ
p ÷q q = p * invℚ q

------------------------------------------------------------------------
-- 2. Exact local j-expression on the existing short-Weierstrass carrier.
------------------------------------------------------------------------

oneSevenTwoEight : ℚ
oneSevenTwoEight = Elliptic.sixtyFour * Elliptic.twentySeven

oneSevenTwoEightIsSixtyFourTimesTwentySeven :
  oneSevenTwoEight ≡ Elliptic.sixtyFour * Elliptic.twentySeven
oneSevenTwoEightIsSixtyFourTimesTwentySeven = refl

shortJDenominator : Elliptic.ShortWeierstrassCurve → ℚ
shortJDenominator curve =
  Elliptic.four
    * Elliptic.aCoefficient curve
    * Elliptic.aCoefficient curve
    * Elliptic.aCoefficient curve
  + Elliptic.twentySeven
    * Elliptic.bCoefficient curve
    * Elliptic.bCoefficient curve

shortJNumerator : Elliptic.ShortWeierstrassCurve → ℚ
shortJNumerator curve =
  oneSevenTwoEight
  * Elliptic.four
  * Elliptic.aCoefficient curve
  * Elliptic.aCoefficient curve
  * Elliptic.aCoefficient curve

shortWeierstrassJExpression : Elliptic.ShortWeierstrassCurve → ℚ
shortWeierstrassJExpression curve =
  shortJNumerator curve ÷q shortJDenominator curve

------------------------------------------------------------------------
-- 3. The existing discriminant receipt certifies the denominator is nonzero.
------------------------------------------------------------------------

shortJDenominatorMatchesDiscriminantCore :
  (curve : Elliptic.ShortWeierstrassCurve) →
  shortJDenominator curve
  ≡ Elliptic.four
      * Elliptic.aCoefficient curve
      * Elliptic.aCoefficient curve
      * Elliptic.aCoefficient curve
    + Elliptic.twentySeven
      * Elliptic.bCoefficient curve
      * Elliptic.bCoefficient curve
shortJDenominatorMatchesDiscriminantCore curve = refl

shortJDenominatorNonzero :
  (curve : Elliptic.ShortWeierstrassCurve) →
  shortJDenominator curve ≡ 0ℚ →
  ⊥
shortJDenominatorNonzero curve denominatorZero =
  Elliptic.discriminantNonzero curve
    (Eq.trans
      (Eq.cong
        (λ denominator → (- Elliptic.sixteen) * denominator)
        denominatorZero)
      (ℚRing.solve-∀ Elliptic.sixteen))

------------------------------------------------------------------------
-- 4. A=0 forces the exact short-form j-expression to zero.
------------------------------------------------------------------------

aZeroShortJNumeratorIsZero :
  ∀ {curve} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  shortJNumerator curve ≡ 0ℚ
aZeroShortJNumeratorIsZero {curve} refl =
  ℚRing.solve-∀ oneSevenTwoEight Elliptic.four

aZeroShortJExpressionIsZero :
  ∀ {curve} →
  Elliptic.aCoefficient curve ≡ 0ℚ →
  shortWeierstrassJExpression curve ≡ 0ℚ
aZeroShortJExpressionIsZero {curve} aZero =
  Eq.trans
    (Eq.cong
      (λ numerator → numerator * invℚ (shortJDenominator curve))
      (aZeroShortJNumeratorIsZero aZero))
    (ℚRing.solve-∀ (invℚ (shortJDenominator curve)))

------------------------------------------------------------------------
-- 5. Attribution and promotion boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record EisensteinAZeroJInvariantBoundary : Set where
  constructor eisenstein-a-zero-j-invariant-boundary
  field
    shortJExpressionDefined : Bool
    discriminantDenominatorNonzeroPaid : Bool
    aZeroJExpressionZeroPaid : Bool
    classicalJInvariantIdentificationPromotedBeyondThisExpression : Bool
    fullCMEndomorphismRingPaid : Bool
    heckeCharacterPaid : Bool
    ellipticLSeriesIdentifiedWithChiMinus3 : Bool
    externalScientificSourceAcquiredByThisOwner : Bool

open EisensteinAZeroJInvariantBoundary public

canonicalBoundary : EisensteinAZeroJInvariantBoundary
canonicalBoundary =
  eisenstein-a-zero-j-invariant-boundary
    true
    true
    true
    false
    false
    false
    false
    false
