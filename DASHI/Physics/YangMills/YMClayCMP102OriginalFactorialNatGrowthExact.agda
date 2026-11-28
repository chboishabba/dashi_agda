module DASHI.Physics.YangMills.YMClayCMP102OriginalFactorialNatGrowthExact where

------------------------------------------------------------------------
-- Genuine Nat factorial denominator growth, not a floating-point
-- sample and not an assumed geometric ratio.
--
-- Original CMP102 A denominator: (2n+2)!,
--   12*(2n+2)! <= (2n+4)!.
-- Original CMP102 B denominator: (2n+3)!,
--   20*(2n+3)! <= (2n+5)!.
--
-- These are the EXACT all-index Nat cross-multiplication inequalities
-- needed by the rational/Bishop real successor-ratio receiver.
-- Only the final Nat->unnormalised-rational multiplication/order
-- bridge is then needed to discharge OriginalARatio/BRatio.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as N
open N using (z≤n; s≤s)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using (subst)
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E

aDenominatorFactorProductLower :
  ∀ k →
  12 N.≤
    (suc (suc (suc (suc k)))) N.*
    (suc (suc (suc k)))
aDenominatorFactorProductLower k =
  NP.*-mono-≤
    (s≤s (s≤s (s≤s (s≤s z≤n))))
    (s≤s (s≤s (s≤s z≤n)))

bDenominatorFactorProductLower :
  ∀ k → suc zero N.≤ k →
  20 N.≤
    (suc (suc (suc (suc k)))) N.*
    (suc (suc (suc k)))
bDenominatorFactorProductLower k kpos =
  NP.*-mono-≤
    (s≤s (s≤s (s≤s (s≤s kpos))))
    (s≤s (s≤s (s≤s kpos)))

aFactorialTwoStepLower :
  ∀ k →
  12 N.* E.factorial (suc (suc k)) N.≤
    E.factorial (suc (suc (suc (suc k))))
aFactorialTwoStepLower k =
  let
    first = suc (suc (suc (suc k)))
    second = suc (suc (suc k))
    old = E.factorial (suc (suc k))
    raw = NP.*-mono-≤
      (aDenominatorFactorProductLower k)
      (NP.≤-refl {n = old})
  in subst
    (λ v → (12 N.* old) N.≤ v)
    (NP.*-assoc first second old)
    raw

bFactorialTwoStepLower :
  ∀ k → suc zero N.≤ k →
  20 N.* E.factorial (suc (suc k)) N.≤
    E.factorial (suc (suc (suc (suc k))))
bFactorialTwoStepLower k kpos =
  let
    first = suc (suc (suc (suc k)))
    second = suc (suc (suc k))
    old = E.factorial (suc (suc k))
    raw = NP.*-mono-≤
      (bDenominatorFactorProductLower k kpos)
      (NP.≤-refl {n = old})
  in subst
    (λ v → (20 N.* old) N.≤ v)
    (NP.*-assoc first second old)
    raw

oddExponentAtLeastOne : ∀ n → suc zero N.≤ E.oddExponent n
oddExponentAtLeastOne zero = s≤s z≤n
oddExponentAtLeastOne (suc n) = s≤s z≤n

-- Original even exponent at successor is 2 + evenExponent n.
-- Therefore its factorial next step is bounded below by 12.
originalADenominatorGrowth :
  ∀ n →
  12 N.* E.factorial (E.evenExponent (suc n)) N.≤
    E.factorial (E.evenExponent (suc (suc n)))
originalADenominatorGrowth n =
  aFactorialTwoStepLower (E.evenExponent n)

-- Original odd exponent at successor is 2 + oddExponent n,
-- where oddExponent n >= 1; its two-step denominator factor is
-- therefore at least 5*4 = 20 at every n including zero.
originalBDenominatorGrowth :
  ∀ n →
  20 N.* E.factorial (E.oddExponent (suc n)) N.≤
    E.factorial (E.oddExponent (suc (suc n)))
originalBDenominatorGrowth n =
  bFactorialTwoStepLower
    (E.oddExponent n) (oddExponentAtLeastOne n)
