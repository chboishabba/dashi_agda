module DASHI.ComputerScience.TekumParsedExactTriadicWeldExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; _+_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- SAME-OBJECT WELD FOR PROP. 2
--
-- The rational uniqueness proof must act on the literal ExactTriadic produced
-- by Source.ordinaryFromParsed, not on a parallel source formula.  This owner
-- exposes the definitional coordinates of that exact object and welds each
-- coordinate back to the parsed source fields.
------------------------------------------------------------------------

exactPow3MatchesBalancedPow3 :
  (n : Nat) → Exact.pow3 n ≡ BT.pow3 n
exactPow3MatchesBalancedPow3 zero = refl
exactPow3MatchesBalancedPow3 (suc n)
  rewrite exactPow3MatchesBalancedPow3 n = refl

parsedExactBaseUnit :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Exact.baseUnit
    (Exact.significand
      (Exact.ordinaryExactTriadic
        (Source.ordinaryFromParsed word parsed)))
  ≡ BT.pow3 (Regime.fractionCount (8 + extra) r)
parsedExactBaseUnit {extra} {r} word parsed =
  exactPow3MatchesBalancedPow3 (Regime.fractionCount (8 + extra) r)

parsedExactAdjustmentInteger :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Exact.intCodeToInteger
    (Exact.adjustment
      (Exact.significand
        (Exact.ordinaryExactTriadic
          (Source.ordinaryFromParsed word parsed))))
  ≡ BT.toInteger (BT.eval (Source.fractionLST parsed))
parsedExactAdjustmentInteger word parsed =
  Source.fractionIntCodeInteger parsed

parsedExactScale :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  Exact.scale
    (Exact.ordinaryExactTriadic
      (Source.ordinaryFromParsed word parsed))
  ≡ Exact.intCodeScale
      (Source.exponentIntCode parsed)
      (Regime.fractionCount (8 + extra) r)
parsedExactScale word parsed = refl

unsignedExactSignificandInteger : Exact.ExactTriadic → ℤ
unsignedExactSignificandInteger x =
  (+ (Exact.baseUnit (Exact.significand x)))
  ℤ.+ Exact.intCodeToInteger (Exact.adjustment (Exact.significand x))

cong₂ :
  ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} →
  x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

parsedExactUnsignedSignificandInteger :
  ∀ {extra r payload}
  (word : Vec Trit.Trit (8 + extra))
  (parsed : Source.ParsedPayload extra r payload) →
  unsignedExactSignificandInteger
    (Exact.ordinaryExactTriadic
      (Source.ordinaryFromParsed word parsed))
  ≡ (+ (BT.pow3 (Regime.fractionCount (8 + extra) r)))
      ℤ.+ BT.toInteger (BT.eval (Source.fractionLST parsed))
parsedExactUnsignedSignificandInteger word parsed =
  cong₂ ℤ._+_
    (cong +_ (parsedExactBaseUnit word parsed))
    (parsedExactAdjustmentInteger word parsed)
