module DASHI.ComputerScience.TekumRegimeExponentIntervalExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; -[1+_]; -_; _+_; _≤_; _<_; +≤+; -≤+; +<+; -<+; -<-)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (z≤n)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFractionRangeExact as Range
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumTriadicScaleExact as Scale

------------------------------------------------------------------------
-- REGIME EXPONENT INTERVALS
--
-- For regime r with c(r) exponent trits and bias b(r), the parser exponent
-- belongs to the exact integer block
--
--   [ b(r) - A_c , b(r) + A_c ].
--
-- The fifteen source biases were chosen so that successive blocks are
-- adjacent and non-overlapping.
------------------------------------------------------------------------

regimeBiasInteger : Regime.RegimeCode → ℤ
regimeBiasInteger r = Exact.intCodeToInteger (Regime.bias r)

regimeRadius : Regime.RegimeCode → Nat
regimeRadius r = Positional.center (Regime.exponentCount r)

regimeLower : Regime.RegimeCode → ℤ
regimeLower r =
  (ℤ.- (+ (regimeRadius r))) ℤ.+ regimeBiasInteger r

regimeUpper : Regime.RegimeCode → ℤ
regimeUpper r =
  (+ (regimeRadius r)) ℤ.+ regimeBiasInteger r

parsedExponentInteger :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → ℤ
parsedExponentInteger parsed =
  Exact.intCodeToInteger (Source.exponentIntCode parsed)

parsedExponentLower :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  regimeLower r ≤ parsedExponentInteger parsed
parsedExponentLower {r = r} parsed =
  subst
    (λ z → regimeLower r ≤ z)
    (sym (Source.exponentIntCodeInteger parsed))
    (ℤP.+-monoˡ-≤
      (regimeBiasInteger r)
      (Range.fractionIntegerLower (Source.exponentLST parsed)))

parsedExponentUpper :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  parsedExponentInteger parsed ≤ regimeUpper r
parsedExponentUpper {r = r} parsed =
  subst
    (λ z → z ≤ regimeUpper r)
    (sym (Source.exponentIntCodeInteger parsed))
    (ℤP.+-monoˡ-≤
      (regimeBiasInteger r)
      (Range.fractionIntegerUpper (Source.exponentLST parsed)))

parsedExponentRange :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  (regimeLower r ≤ parsedExponentInteger parsed)
  × (parsedExponentInteger parsed ≤ regimeUpper r)
parsedExponentRange parsed =
  parsedExponentLower parsed , parsedExponentUpper parsed

------------------------------------------------------------------------
-- Every interval is nonempty.
------------------------------------------------------------------------

negativeCenterLePositiveCenter :
  (n : Nat) → ℤ.- (+ n) ≤ + n
negativeCenterLePositiveCenter zero = +≤+ z≤n
negativeCenterLePositiveCenter (suc n) = -≤+

regimeIntervalNonempty :
  (r : Regime.RegimeCode) →
  regimeLower r ≤ regimeUpper r
regimeIntervalNonempty r =
  ℤP.+-monoˡ-≤
    (regimeBiasInteger r)
    (negativeCenterLePositiveCenter (regimeRadius r))

------------------------------------------------------------------------
-- The source table is one contiguous chain of exponent blocks.
------------------------------------------------------------------------

data RegimeStep : Regime.RegimeCode → Regime.RegimeCode → Set where
  step-rm7-rm6 : RegimeStep Regime.rm7 Regime.rm6
  step-rm6-rm5 : RegimeStep Regime.rm6 Regime.rm5
  step-rm5-rm4 : RegimeStep Regime.rm5 Regime.rm4
  step-rm4-rm3 : RegimeStep Regime.rm4 Regime.rm3
  step-rm3-rm2 : RegimeStep Regime.rm3 Regime.rm2
  step-rm2-rm1 : RegimeStep Regime.rm2 Regime.rm1
  step-rm1-r0  : RegimeStep Regime.rm1 Regime.r0
  step-r0-rp1  : RegimeStep Regime.r0 Regime.rp1
  step-rp1-rp2 : RegimeStep Regime.rp1 Regime.rp2
  step-rp2-rp3 : RegimeStep Regime.rp2 Regime.rp3
  step-rp3-rp4 : RegimeStep Regime.rp3 Regime.rp4
  step-rp4-rp5 : RegimeStep Regime.rp4 Regime.rp5
  step-rp5-rp6 : RegimeStep Regime.rp5 Regime.rp6
  step-rp6-rp7 : RegimeStep Regime.rp6 Regime.rp7

adjacentRegimeBoundary :
  ∀ {r s} → RegimeStep r s →
  regimeLower s ≡ Scale.integerSucc (regimeUpper r)
adjacentRegimeBoundary step-rm7-rm6 = refl
adjacentRegimeBoundary step-rm6-rm5 = refl
adjacentRegimeBoundary step-rm5-rm4 = refl
adjacentRegimeBoundary step-rm4-rm3 = refl
adjacentRegimeBoundary step-rm3-rm2 = refl
adjacentRegimeBoundary step-rm2-rm1 = refl
adjacentRegimeBoundary step-rm1-r0 = refl
adjacentRegimeBoundary step-r0-rp1 = refl
adjacentRegimeBoundary step-rp1-rp2 = refl
adjacentRegimeBoundary step-rp2-rp3 = refl
adjacentRegimeBoundary step-rp3-rp4 = refl
adjacentRegimeBoundary step-rp4-rp5 = refl
adjacentRegimeBoundary step-rp5-rp6 = refl
adjacentRegimeBoundary step-rp6-rp7 = refl

integerLessSuccessor :
  (z : ℤ) → z < Scale.integerSucc z
integerLessSuccessor (+ n) = +<+ (NatP.n<1+n n)
integerLessSuccessor -[1+ zero ] = -<+
integerLessSuccessor -[1+ suc n ] = -<- (NatP.n<1+n n)

stepRegimeIntervalsOrdered :
  ∀ {r s} → RegimeStep r s →
  regimeUpper r < regimeLower s
stepRegimeIntervalsOrdered {r} {s} step =
  subst
    (λ z → regimeUpper r < z)
    (sym (adjacentRegimeBoundary step))
    (integerLessSuccessor (regimeUpper r))
