module DASHI.ComputerScience.TekumParsedExactRationalCoordinatesExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; _+_; _*_)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base as ℚ using (ℚ; _/_)
open import Data.Vec using (Vec)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Foundations.BinaryFloatingPoint as Binary
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumParsedExactTriadicWeldExact as Weld

------------------------------------------------------------------------
-- Exact numerator/denominator coordinates of the literal parser decoder.
--
-- This is the last purely representational step before the Prop. 2 rational
-- factorisation.  Nothing here introduces a parallel value semantics: every
-- theorem is stated directly about Exact.ordinaryExactTriadic applied to
-- Source.ordinaryFromParsed.
------------------------------------------------------------------------

parsedSourceScale :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  Binary.SignedScale
parsedSourceScale {extra} {r = r} parsed =
  Exact.intCodeScale
    (Source.exponentIntCode parsed)
    (Regime.fractionCount (8 + extra) r)

parsedSourceUnsignedNumerator :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  ℤ
parsedSourceUnsignedNumerator {extra} {r = r} parsed =
  ((+ (BT.pow3 (Regime.fractionCount (8 + extra) r)))
    ℤ.+ BT.toInteger (BT.eval (Source.fractionLST parsed)))
  ℤ.* (+ (Exact.pow3 (Binary.positivePart (parsedSourceScale parsed))))

parsedSourceNumerator :
  ∀ {extra r payload} →
  Vec Trit.Trit (8 + extra) →
  Source.ParsedPayload extra r payload →
  ℤ
parsedSourceNumerator word parsed =
  Exact.applySign (Source.signOfWord word)
    (parsedSourceUnsignedNumerator parsed)

parsedSourceDenominator :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  _
parsedSourceDenominator parsed =
  Exact.pow3 (Binary.negativePart (parsedSourceScale parsed))

parsedExactNumeratorUsesSourceCoordinates :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Exact.exactTriadicNumerator
    (Exact.ordinaryExactTriadic
      (Source.ordinaryFromParsed word parsed))
  ≡ parsedSourceNumerator word parsed
parsedExactNumeratorUsesSourceCoordinates word parsed
  rewrite Weld.parsedExactScale word parsed
        | Weld.parsedExactUnsignedSignificandInteger word parsed = refl

parsedExactDenominatorUsesSourceCoordinates :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Exact.exactTriadicDenominator
    (Exact.ordinaryExactTriadic
      (Source.ordinaryFromParsed word parsed))
  ≡ parsedSourceDenominator parsed
parsedExactDenominatorUsesSourceCoordinates word parsed
  rewrite Weld.parsedExactScale word parsed = refl

parsedSourceDenominatorNonZero :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  NonZero (parsedSourceDenominator parsed)
parsedSourceDenominatorNonZero parsed =
  Exact.pow3NonZero
    (Binary.negativePart (parsedSourceScale parsed))

parsedOrdinaryRationalUsesExactSourceCoordinates :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Source.ordinaryRationalFromParsed word parsed
  ≡ let instance denominatorNonZero = parsedSourceDenominatorNonZero parsed
     in parsedSourceNumerator word parsed ℚ./ parsedSourceDenominator parsed
parsedOrdinaryRationalUsesExactSourceCoordinates word parsed
  rewrite parsedExactNumeratorUsesSourceCoordinates word parsed
        | parsedExactDenominatorUsesSourceCoordinates word parsed = refl
