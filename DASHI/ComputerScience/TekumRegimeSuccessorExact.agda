module DASHI.ComputerScience.TekumRegimeSuccessorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using (Vec)
open import Data.Vec.Base using (reverse)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumRegimeExponentIntervalExact as Interval
import DASHI.ComputerScience.TekumSourceWordRoundTripExact as RoundTrip

------------------------------------------------------------------------
-- The three regime trits form a literal balanced-ternary counter from rm7 to
-- rp7. In LST-first orientation, one balanced successor takes every non-top
-- regime prefix to the next row of the source table.
------------------------------------------------------------------------

regimeLST : Regime.RegimeCode → Vec Trit.Trit 3
regimeLST r = reverse (RoundTrip.regimePrefixMSB r)

data RegimeSuccessor : Regime.RegimeCode → Set where
  next-rm7 : RegimeSuccessor Regime.rm7
  next-rm6 : RegimeSuccessor Regime.rm6
  next-rm5 : RegimeSuccessor Regime.rm5
  next-rm4 : RegimeSuccessor Regime.rm4
  next-rm3 : RegimeSuccessor Regime.rm3
  next-rm2 : RegimeSuccessor Regime.rm2
  next-rm1 : RegimeSuccessor Regime.rm1
  next-r0  : RegimeSuccessor Regime.r0
  next-rp1 : RegimeSuccessor Regime.rp1
  next-rp2 : RegimeSuccessor Regime.rp2
  next-rp3 : RegimeSuccessor Regime.rp3
  next-rp4 : RegimeSuccessor Regime.rp4
  next-rp5 : RegimeSuccessor Regime.rp5
  next-rp6 : RegimeSuccessor Regime.rp6

nextRegime :
  (r : Regime.RegimeCode) → RegimeSuccessor r → Regime.RegimeCode
nextRegime Regime.rm7 next-rm7 = Regime.rm6
nextRegime Regime.rm6 next-rm6 = Regime.rm5
nextRegime Regime.rm5 next-rm5 = Regime.rm4
nextRegime Regime.rm4 next-rm4 = Regime.rm3
nextRegime Regime.rm3 next-rm3 = Regime.rm2
nextRegime Regime.rm2 next-rm2 = Regime.rm1
nextRegime Regime.rm1 next-rm1 = Regime.r0
nextRegime Regime.r0  next-r0  = Regime.rp1
nextRegime Regime.rp1 next-rp1 = Regime.rp2
nextRegime Regime.rp2 next-rp2 = Regime.rp3
nextRegime Regime.rp3 next-rp3 = Regime.rp4
nextRegime Regime.rp4 next-rp4 = Regime.rp5
nextRegime Regime.rp5 next-rp5 = Regime.rp6
nextRegime Regime.rp6 next-rp6 = Regime.rp7

regimeStep :
  ∀ {r} (w : RegimeSuccessor r) → Interval.RegimeStep r (nextRegime r w)
regimeStep next-rm7 = Interval.step-rm7-rm6
regimeStep next-rm6 = Interval.step-rm6-rm5
regimeStep next-rm5 = Interval.step-rm5-rm4
regimeStep next-rm4 = Interval.step-rm4-rm3
regimeStep next-rm3 = Interval.step-rm3-rm2
regimeStep next-rm2 = Interval.step-rm2-rm1
regimeStep next-rm1 = Interval.step-rm1-r0
regimeStep next-r0  = Interval.step-r0-rp1
regimeStep next-rp1 = Interval.step-rp1-rp2
regimeStep next-rp2 = Interval.step-rp2-rp3
regimeStep next-rp3 = Interval.step-rp3-rp4
regimeStep next-rp4 = Interval.step-rp4-rp5
regimeStep next-rp5 = Interval.step-rp5-rp6
regimeStep next-rp6 = Interval.step-rp6-rp7

regimeHasBalancedSuccessor :
  ∀ {r} (w : RegimeSuccessor r) → Succ.HasSuccessor (regimeLST r)
regimeHasBalancedSuccessor next-rm7 = Succ.negativeHead
regimeHasBalancedSuccessor next-rm6 = Succ.zeroHead
regimeHasBalancedSuccessor next-rm5 = Succ.positiveCarry Succ.negativeHead
regimeHasBalancedSuccessor next-rm4 = Succ.negativeHead
regimeHasBalancedSuccessor next-rm3 = Succ.zeroHead
regimeHasBalancedSuccessor next-rm2 = Succ.positiveCarry Succ.negativeHead
regimeHasBalancedSuccessor next-rm1 = Succ.negativeHead
regimeHasBalancedSuccessor next-r0  = Succ.zeroHead
regimeHasBalancedSuccessor next-rp1 = Succ.positiveCarry Succ.negativeHead
regimeHasBalancedSuccessor next-rp2 = Succ.negativeHead
regimeHasBalancedSuccessor next-rp3 = Succ.zeroHead
regimeHasBalancedSuccessor next-rp4 = Succ.positiveCarry Succ.negativeHead
regimeHasBalancedSuccessor next-rp5 = Succ.negativeHead
regimeHasBalancedSuccessor next-rp6 = Succ.zeroHead

regimeWordSuccessor :
  ∀ {r} (w : RegimeSuccessor r) →
  Succ.successorWord (regimeLST r) ≡ regimeLST (nextRegime r w)
regimeWordSuccessor next-rm7 = refl
regimeWordSuccessor next-rm6 = refl
regimeWordSuccessor next-rm5 = refl
regimeWordSuccessor next-rm4 = refl
regimeWordSuccessor next-rm3 = refl
regimeWordSuccessor next-rm2 = refl
regimeWordSuccessor next-rm1 = refl
regimeWordSuccessor next-r0  = refl
regimeWordSuccessor next-rp1 = refl
regimeWordSuccessor next-rp2 = refl
regimeWordSuccessor next-rp3 = refl
regimeWordSuccessor next-rp4 = refl
regimeWordSuccessor next-rp5 = refl
regimeWordSuccessor next-rp6 = refl

regimeExponentBlocksStrictlyIncrease :
  ∀ {r} (w : RegimeSuccessor r) →
  Interval.regimeUpper r Interval.< Interval.regimeLower (nextRegime r w)
regimeExponentBlocksStrictlyIncrease w =
  Interval.stepRegimeIntervalsOrdered (regimeStep w)
