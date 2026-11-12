module DASHI.Analysis.RiemannEtaZetaOriginalFinitePairingExact where

------------------------------------------------------------------------
-- P2 finite (non-analytic) eta--zeta parity payment.
--
-- On the EXISTING original rational complex carrier Q[i], for an
-- ARBITRARY Nat-indexed source term f, pair terms f(2k), f(2k+1).
--
--   eta(2N) + 2 * sum_{k<N} f(2k+1) = zeta(2N)
--
-- Here f(n) denotes the prospective Dirichlet term at n+1, so the
-- odd array index 2k+1 is the EVEN POSITIVE integer 2k+2.
-- This is exact finite ring algebra with a fully generic term input.
--
-- Analytic source identification of f(n)=(n+1)^(-s), the limit
-- N→∞, rescaling of the even subsequence, nonvanishing/removable
-- singularities of 1-2^(1-s), and actual zeta continuation
-- remain independent, unpaid ORIGINAL BISHOP analytic theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD

twoIndex : Nat → Nat
twoIndex n = n + n

-- The generic prefix uses the ORIGINAL rational-complex addition.
prefix :
  (Nat → CD.RationalComplex) → Nat → CD.RationalComplex
prefix term zero = CD.zeroC
prefix term (suc n) =
  CD._+c_ (prefix term n) (term n)

alternatingPair :
  (Nat → CD.RationalComplex) → Nat → CD.RationalComplex
alternatingPair term n =
  CD._-c_ (term (twoIndex n)) (term (suc (twoIndex n)))

unsignedPair :
  (Nat → CD.RationalComplex) → Nat → CD.RationalComplex
unsignedPair term n =
  CD._+c_ (term (twoIndex n)) (term (suc (twoIndex n)))

evenPositiveTerm :
  (Nat → CD.RationalComplex) → Nat → CD.RationalComplex
evenPositiveTerm term n = term (suc (twoIndex n))

finiteEta finiteZeta finiteEvenPositive :
  (Nat → CD.RationalComplex) → Nat → CD.RationalComplex
finiteEta term n = prefix (alternatingPair term) n
finiteZeta term n = prefix (unsignedPair term) n
finiteEvenPositive term n = prefix (evenPositiveTerm term) n

-- One original Q[i] finite reindexing step; no infinite sums.
finiteEtaPairAlgebra :
  (eta even a b : CD.RationalComplex) →
  CD._+c_
    (CD._+c_ eta (CD._-c_ a b))
    (CD._+c_ (CD._+c_ even b)
              (CD._+c_ even b))
  ≡
  CD._+c_
    (CD._+c_ eta (CD._+c_ even even))
    (CD._+c_ a b)
finiteEtaPairAlgebra
  (CD.complex er ei) (CD.complex vr vi)
  (CD.complex ar ai) (CD.complex br bi) =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

-- Exact result at EVERY finite cutoff and EVERY source term.
finiteEtaPlusTwiceEvenIsZeta :
  (term : Nat → CD.RationalComplex) →
  (n : Nat) →
  CD._+c_
    (finiteEta term n)
    (CD._+c_ (finiteEvenPositive term n)
              (finiteEvenPositive term n))
  ≡ finiteZeta term n
finiteEtaPlusTwiceEvenIsZeta term zero =
  CD.complexExt Ring.solve-∀ Ring.solve-∀
finiteEtaPlusTwiceEvenIsZeta term (suc n) =
  trans
    (finiteEtaPairAlgebra
      (finiteEta term n)
      (finiteEvenPositive term n)
      (term (twoIndex n))
      (term (suc (twoIndex n))))
    (cong
      (λ value → CD._+c_ value (unsignedPair term n))
      (finiteEtaPlusTwiceEvenIsZeta term n))

-- A second presentation matches the usual finite eta--zeta
-- expression without using an unproved analytic quotient.
finiteSubtractEvenTwice :
  (eta even : CD.RationalComplex) →
  CD._-c_ (CD._+c_ eta (CD._+c_ even even))
    (CD._+c_ even even)
  ≡ eta
finiteSubtractEvenTwice
  (CD.complex er ei) (CD.complex vr vi) =
  CD.complexExt Ring.solve-∀ Ring.solve-∀

finiteEtaIsZetaMinusTwiceEven :
  (term : Nat → CD.RationalComplex) →
  (n : Nat) →
  CD._-c_
    (finiteZeta term n)
    (CD._+c_ (finiteEvenPositive term n)
              (finiteEvenPositive term n))
  ≡ finiteEta term n
finiteEtaIsZetaMinusTwiceEven term n =
  trans
    (cong
      (λ value → CD._-c_ value
        (CD._+c_ (finiteEvenPositive term n)
                  (finiteEvenPositive term n)))
      (sym (finiteEtaPlusTwiceEvenIsZeta term n)))
    (finiteSubtractEvenTwice
      (finiteEta term n) (finiteEvenPositive term n))

-- In particular, this finite identity is valid independently
-- of whether the supplied sequence converges. It cannot
-- construct eta(s), gamma(s), xi(s), or a zeta pole.
