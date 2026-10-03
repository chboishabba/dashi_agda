module DASHI.ComputerScience.TekumRegimeChainExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; -[1+_]; _≤_; _<_)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as NatP
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.ComputerScience.TekumExponentBandExact as Band
import DASHI.ComputerScience.TekumIntegerSuccessorGapExact as Gap
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumRegimeExponentIntervalExact as Interval
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- THE FIFTEEN REGIME INTERVALS AS ONE CONTIGUOUS CHAIN
--
-- The interval cardinalities are the exponent-field state counts:
--
--   243,81,27,9,3,1,1,1,1,1,3,9,27,81,243.
--
-- Encoding each block by its predecessor count makes adjacency definitional:
-- lower(i+1) = succ(upper(i)).
------------------------------------------------------------------------

regimeIndex : Regime.RegimeCode → Nat
regimeIndex Regime.rm7 = 0
regimeIndex Regime.rm6 = 1
regimeIndex Regime.rm5 = 2
regimeIndex Regime.rm4 = 3
regimeIndex Regime.rm3 = 4
regimeIndex Regime.rm2 = 5
regimeIndex Regime.rm1 = 6
regimeIndex Regime.r0  = 7
regimeIndex Regime.rp1 = 8
regimeIndex Regime.rp2 = 9
regimeIndex Regime.rp3 = 10
regimeIndex Regime.rp4 = 11
regimeIndex Regime.rp5 = 12
regimeIndex Regime.rp6 = 13
regimeIndex Regime.rp7 = 14

regimeFromIndex : Nat → Regime.RegimeCode
regimeFromIndex 0 = Regime.rm7
regimeFromIndex 1 = Regime.rm6
regimeFromIndex 2 = Regime.rm5
regimeFromIndex 3 = Regime.rm4
regimeFromIndex 4 = Regime.rm3
regimeFromIndex 5 = Regime.rm2
regimeFromIndex 6 = Regime.rm1
regimeFromIndex 7 = Regime.r0
regimeFromIndex 8 = Regime.rp1
regimeFromIndex 9 = Regime.rp2
regimeFromIndex 10 = Regime.rp3
regimeFromIndex 11 = Regime.rp4
regimeFromIndex 12 = Regime.rp5
regimeFromIndex 13 = Regime.rp6
regimeFromIndex 14 = Regime.rp7
regimeFromIndex _ = Regime.r0

regimeFromIndexRoundTrip :
  (r : Regime.RegimeCode) → regimeFromIndex (regimeIndex r) ≡ r
regimeFromIndexRoundTrip Regime.rm7 = refl
regimeFromIndexRoundTrip Regime.rm6 = refl
regimeFromIndexRoundTrip Regime.rm5 = refl
regimeFromIndexRoundTrip Regime.rm4 = refl
regimeFromIndexRoundTrip Regime.rm3 = refl
regimeFromIndexRoundTrip Regime.rm2 = refl
regimeFromIndexRoundTrip Regime.rm1 = refl
regimeFromIndexRoundTrip Regime.r0 = refl
regimeFromIndexRoundTrip Regime.rp1 = refl
regimeFromIndexRoundTrip Regime.rp2 = refl
regimeFromIndexRoundTrip Regime.rp3 = refl
regimeFromIndexRoundTrip Regime.rp4 = refl
regimeFromIndexRoundTrip Regime.rp5 = refl
regimeFromIndexRoundTrip Regime.rp6 = refl
regimeFromIndexRoundTrip Regime.rp7 = refl

regimeIndexInjective :
  ∀ {r s} → regimeIndex r ≡ regimeIndex s → r ≡ s
regimeIndexInjective {r} {s} eq =
  trans
    (sym (regimeFromIndexRoundTrip r))
    (trans
      (cong regimeFromIndex eq)
      (regimeFromIndexRoundTrip s))

spanPredAtIndex : Nat → Nat
spanPredAtIndex 0 = 242
spanPredAtIndex 1 = 80
spanPredAtIndex 2 = 26
spanPredAtIndex 3 = 8
spanPredAtIndex 4 = 2
spanPredAtIndex 5 = 0
spanPredAtIndex 6 = 0
spanPredAtIndex 7 = 0
spanPredAtIndex 8 = 0
spanPredAtIndex 9 = 0
spanPredAtIndex 10 = 2
spanPredAtIndex 11 = 8
spanPredAtIndex 12 = 26
spanPredAtIndex 13 = 80
spanPredAtIndex 14 = 242
spanPredAtIndex _ = 0

chainLower : Nat → ℤ
chainLower zero = -[1+ 364 ]
chainLower (suc i) =
  Band.advanceExponent (suc (spanPredAtIndex i)) (chainLower i)

chainUpper : Nat → ℤ
chainUpper i =
  Band.advanceExponent (spanPredAtIndex i) (chainLower i)

chainStepBoundary :
  (i : Nat) →
  chainLower (suc i) ≡
  DASHI.ComputerScience.TekumTriadicScaleExact.integerSucc (chainUpper i)
chainStepBoundary i = refl

advanceNondecreasing :
  (n : Nat) (e : ℤ) →
  e ≤ Band.advanceExponent n e
advanceNondecreasing zero e = ℤP.≤-refl
advanceNondecreasing (suc n) e =
  ℤP.≤-trans
    (advanceNondecreasing n e)
    (ℤP.<⇒≤
      (Interval.integerLessSuccessor (Band.advanceExponent n e)))

chainIntervalNonempty :
  (i : Nat) →
  chainLower i ≤ chainUpper i
chainIntervalNonempty i =
  advanceNondecreasing (spanPredAtIndex i) (chainLower i)

chainStepOrdered :
  (i : Nat) →
  chainUpper i < chainLower (suc i)
chainStepOrdered i =
  subst
    (λ z → chainUpper i < z)
    (sym (chainStepBoundary i))
    (Interval.integerLessSuccessor (chainUpper i))

chainUpperBeforeOffset :
  (i k : Nat) →
  chainUpper i < chainLower (i + suc k)
chainUpperBeforeOffset i zero =
  subst
    (λ j → chainUpper i < chainLower j)
    (sym oneStep)
    (chainStepOrdered i)
  where
  oneStep : i + suc zero ≡ suc i
  oneStep =
    trans
      (NatP.+-suc i zero)
      (cong suc (NatP.+-identityʳ i))
chainUpperBeforeOffset i (suc k) =
  subst
    (λ j → chainUpper i < chainLower j)
    (sym (NatP.+-suc i (suc k)))
    (ℤP.<-trans
      (ℤP.<-≤-trans
        (chainUpperBeforeOffset i k)
        (chainIntervalNonempty (i + suc k)))
      (chainStepOrdered (i + suc k)))

chainIntervalsOrderedFromLess :
  ∀ {i j : Nat} →
  i NatP.< j →
  chainUpper i < chainLower j
chainIntervalsOrderedFromLess {i} {j} i<j
  with Gap.natStrictGap i<j
... | k , eq =
  subst
    (λ q → chainUpper i < chainLower q)
    eq
    (chainUpperBeforeOffset i k)

------------------------------------------------------------------------
-- The source bias-derived intervals are exactly this chain.
------------------------------------------------------------------------

regimeLowerMatchesChain :
  (r : Regime.RegimeCode) →
  Interval.regimeLower r ≡ chainLower (regimeIndex r)
regimeLowerMatchesChain Regime.rm7 = refl
regimeLowerMatchesChain Regime.rm6 = refl
regimeLowerMatchesChain Regime.rm5 = refl
regimeLowerMatchesChain Regime.rm4 = refl
regimeLowerMatchesChain Regime.rm3 = refl
regimeLowerMatchesChain Regime.rm2 = refl
regimeLowerMatchesChain Regime.rm1 = refl
regimeLowerMatchesChain Regime.r0 = refl
regimeLowerMatchesChain Regime.rp1 = refl
regimeLowerMatchesChain Regime.rp2 = refl
regimeLowerMatchesChain Regime.rp3 = refl
regimeLowerMatchesChain Regime.rp4 = refl
regimeLowerMatchesChain Regime.rp5 = refl
regimeLowerMatchesChain Regime.rp6 = refl
regimeLowerMatchesChain Regime.rp7 = refl

regimeUpperMatchesChain :
  (r : Regime.RegimeCode) →
  Interval.regimeUpper r ≡ chainUpper (regimeIndex r)
regimeUpperMatchesChain Regime.rm7 = refl
regimeUpperMatchesChain Regime.rm6 = refl
regimeUpperMatchesChain Regime.rm5 = refl
regimeUpperMatchesChain Regime.rm4 = refl
regimeUpperMatchesChain Regime.rm3 = refl
regimeUpperMatchesChain Regime.rm2 = refl
regimeUpperMatchesChain Regime.rm1 = refl
regimeUpperMatchesChain Regime.r0 = refl
regimeUpperMatchesChain Regime.rp1 = refl
regimeUpperMatchesChain Regime.rp2 = refl
regimeUpperMatchesChain Regime.rp3 = refl
regimeUpperMatchesChain Regime.rp4 = refl
regimeUpperMatchesChain Regime.rp5 = refl
regimeUpperMatchesChain Regime.rp6 = refl
regimeUpperMatchesChain Regime.rp7 = refl

regimeIntervalsOrderedFromIndex :
  ∀ {r s} →
  regimeIndex r NatP.< regimeIndex s →
  Interval.regimeUpper r < Interval.regimeLower s
regimeIntervalsOrderedFromIndex {r} {s} order
  rewrite regimeUpperMatchesChain r
        | regimeLowerMatchesChain s =
  chainIntervalsOrderedFromLess order

------------------------------------------------------------------------
-- Total regime comparison and uniqueness of interval membership.
------------------------------------------------------------------------

data RegimeComparison
    (r s : Regime.RegimeCode) : Set where
  same : r ≡ s → RegimeComparison r s
  before :
    Interval.regimeUpper r < Interval.regimeLower s →
    RegimeComparison r s
  after :
    Interval.regimeUpper s < Interval.regimeLower r →
    RegimeComparison r s

compareRegimes :
  (r s : Regime.RegimeCode) → RegimeComparison r s
compareRegimes r s with NatP.<-cmp (regimeIndex r) (regimeIndex s)
... | tri< i<j _ _ = before (regimeIntervalsOrderedFromIndex i<j)
... | tri≈ _ i≡j _ = same (regimeIndexInjective i≡j)
... | tri> _ _ i>j = after (regimeIntervalsOrderedFromIndex i>j)

beforeExponentContradiction :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Interval.regimeUpper r < Interval.regimeLower s →
  Interval.parsedExponentInteger p ≡ Interval.parsedExponentInteger q →
  ⊥
beforeExponentContradiction p q intervalsOrdered exponentEq =
  ℤP.<⇒≢ strict exponentEq
  where
  strict :
    Interval.parsedExponentInteger p
    < Interval.parsedExponentInteger q
  strict =
    ℤP.≤-<-trans
      (Interval.parsedExponentUpper p)
      (ℤP.<-≤-trans
        intervalsOrdered
        (Interval.parsedExponentLower q))

equalParsedExponentForcesRegime :
  ∀ {extra r s payload₁ payload₂}
  (p : Source.ParsedPayload extra r payload₁)
  (q : Source.ParsedPayload extra s payload₂) →
  Interval.parsedExponentInteger p ≡ Interval.parsedExponentInteger q →
  r ≡ s
equalParsedExponentForcesRegime {r = r} {s = s} p q exponentEq
  with compareRegimes r s
... | same r≡s = r≡s
... | before rBeforeS =
  ⊥-elim (beforeExponentContradiction p q rBeforeS exponentEq)
... | after sBeforeR =
  ⊥-elim (beforeExponentContradiction q p sBeforeR (sym exponentEq))
