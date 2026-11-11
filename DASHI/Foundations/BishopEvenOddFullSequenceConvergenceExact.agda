module DASHI.Foundations.BishopEvenOddFullSequenceConvergenceExact where

------------------------------------------------------------------------
-- GENERIC BISHOP FULL-SEQUENCE CONVERGENCE FROM EVEN AND ODD LIMITS.
--
-- Unlike the one-way "subsequence of convergent" theorem, this
-- result combines *both* parity subsequences. It is proved directly
-- from the pinned Bishop Sequence.con* Cauchy moduli and a structural
-- Nat parity cover. One shared threshold 2 max(N_even,N_odd)+1
-- works for all natural indices, with no classical excluded middle.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (proj₁; proj₂)
import Data.Nat.Base as ℕ using (NonZero; _≤_; z≤n; s≤s; _⊔_)
import Data.Nat.Properties as ℕP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as BishopReal
import Sequence as BishopSequence
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates

data ParityCover : Nat → Set where
  even : (n : Nat) → ParityCover (Estimates.evenExponent n)
  odd  : (n : Nat) → ParityCover (suc (Estimates.evenExponent n))

parityCover : (n : Nat) → ParityCover n
parityCover zero = even zero
parityCover (suc zero) = odd zero
parityCover (suc (suc n)) with parityCover n
... | even j = even (suc j)
... | odd j = odd (suc j)

evenIndexLowerBound :
  ∀ N n →
  Estimates.evenExponent N ℕ.≤ Estimates.evenExponent n →
  N ℕ.≤ n
evenIndexLowerBound zero n lower = ℕ.z≤n
evenIndexLowerBound (suc N) zero ()
evenIndexLowerBound (suc N) (suc n)
  (ℕ.s≤s (ℕ.s≤s lower)) =
  ℕ.s≤s (evenIndexLowerBound N n lower)

oddIndexLowerBound :
  ∀ N n →
  Estimates.evenExponent N ℕ.≤ suc (Estimates.evenExponent n) →
  N ℕ.≤ n
oddIndexLowerBound zero n lower = ℕ.z≤n
oddIndexLowerBound (suc N) zero ()
oddIndexLowerBound (suc N) (suc n)
  (ℕ.s≤s (ℕ.s≤s lower)) =
  ℕ.s≤s (oddIndexLowerBound N n lower)

parityBoundAtAnyIndex :
  ∀ {sequence : Nat → BishopReal.ℝ} {limit : BishopReal.ℝ}
    {k N m : Nat} → .{{_ : ℕ.NonZero k}} →
  (evenBound : ∀ n → N ℕ.≤ n →
    BishopReal._≤_
      (BishopReal.∣ BishopReal._-_ 
        (sequence (Estimates.evenExponent n)) limit ∣)
      (BishopReal._⋆ (+ 1 / k))) →
  (oddBound : ∀ n → N ℕ.≤ n →
    BishopReal._≤_
      (BishopReal.∣ BishopReal._-_
        (sequence (suc (Estimates.evenExponent n))) limit ∣)
      (BishopReal._⋆ (+ 1 / k))) →
  ParityCover m →
  suc (Estimates.evenExponent N) ℕ.≤ m →
  BishopReal._≤_
    (BishopReal.∣ BishopReal._-_ (sequence m) limit ∣)
    (BishopReal._⋆ (+ 1 / k))
parityBoundAtAnyIndex {N = N} evenBound oddBound (even n) m≥ =
  evenBound n
    (evenIndexLowerBound N n
      (ℕP.≤-trans
        (ℕP.n≤1+n (Estimates.evenExponent N)) m≥))
parityBoundAtAnyIndex {N = N} evenBound oddBound (odd n) m≥ =
  oddBound n
    (oddIndexLowerBound N n
      (ℕP.≤-trans
        (ℕP.n≤1+n (Estimates.evenExponent N)) m≥))

originalBishopEvenOddLimitsGiveAllCutoffs :
  ∀ (sequence : Nat → BishopReal.ℝ) (limit : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (λ n → sequence (Estimates.evenExponent n))
    limit →
  BishopSequence._ConvergesTo_
    (λ n → sequence (suc (Estimates.evenExponent n)))
    limit →
  BishopSequence._ConvergesTo_ sequence limit
originalBishopEvenOddLimitsGiveAllCutoffs
  sequence limit
  (BishopSequence.con* evenModulus)
  (BishopSequence.con* oddModulus) =
  BishopSequence.con* λ
    { (suc k-1) →
      let
        k = suc k-1
        e = evenModulus k
        o = oddModulus k
        Nₑ = suc (proj₁ e)
        Nₒ = suc (proj₁ o)
        N = Nₑ ℕ.⊔ Nₒ

        eBound : ∀ n → N ℕ.≤ n →
          BishopReal._≤_
            (BishopReal.∣ BishopReal._-_
              (sequence (Estimates.evenExponent n)) limit ∣)
            (BishopReal._⋆ (+ 1 / k))
        eBound n N≤n =
          proj₂ e n
            (ℕP.≤-trans (ℕP.m≤m⊔n Nₑ Nₒ) N≤n)

        oBound : ∀ n → N ℕ.≤ n →
          BishopReal._≤_
            (BishopReal.∣ BishopReal._-_
              (sequence (suc (Estimates.evenExponent n))) limit ∣)
            (BishopReal._⋆ (+ 1 / k))
        oBound n N≤n =
          proj₂ o n
            (ℕP.≤-trans (ℕP.m≤n⊔m Nₑ Nₒ) N≤n)
      in
      Estimates.evenExponent N ,
      λ m m≥ →
        parityBoundAtAnyIndex eBound oBound
          (parityCover m) m≥
    }
