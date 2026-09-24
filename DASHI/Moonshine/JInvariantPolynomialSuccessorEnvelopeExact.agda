module DASHI.Moonshine.JInvariantPolynomialSuccessorEnvelopeExact where

------------------------------------------------------------------------
-- FIXED DEGREE-4 / DEGREE-6 SUCCESSOR ENVELOPES
--
-- DASHI CONTRIBUTION
--
-- This is the finite Nat arithmetic needed by the Eisenstein ratio argument.
-- For n >= 1:
--
--   (n+1)^4 <= n^4 + 15 n^3
--   (n+1)^6 <= n^6 + 63 n^5.
--
-- The constants are deliberately crude: they are just the sums of the
-- non-leading binomial coefficients, after every lower power is bounded by
-- n^(k-1).  This owner is independent of q, Bishop reals and convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Power

powerSuccessorMonotone :
  ∀ {n : Nat} → 1 ≤ n →
  ∀ exponent →
  Power.powNat n exponent ≤ Power.powNat n (suc exponent)
powerSuccessorMonotone {zero} ()
powerSuccessorMonotone {suc n} one≤n exponent =
  NatP.m≤n*m (Power.powNat (suc n) exponent) n

degreeFourExpansion :
  ∀ n →
  Power.powNat (suc n) 4
  ≡
  Power.powNat n 4
    + (4 * Power.powNat n 3
    + (6 * Power.powNat n 2
    + (4 * Power.powNat n 1
    + Power.powNat n 0)))
degreeFourExpansion n =
  solve 1
    (λ x →
      ((con 1 :+ x) :* ((con 1 :+ x) :*
        ((con 1 :+ x) :* ((con 1 :+ x) :* con 1))))
      :=
      (x :* (x :* (x :* (x :* con 1))))
        :+
        ((con 4 :* (x :* (x :* (x :* con 1))))
          :+
          ((con 6 :* (x :* (x :* con 1)))
            :+
            ((con 4 :* (x :* con 1)) :+ con 1))))
    refl n

degreeFourTailCollapse :
  ∀ n →
  4 * Power.powNat n 3
    + (6 * Power.powNat n 3
    + (4 * Power.powNat n 3
    + Power.powNat n 3))
  ≡
  15 * Power.powNat n 3
degreeFourTailCollapse n =
  solve 1
    (λ x →
      (con 4 :* x)
        :+ ((con 6 :* x) :+ ((con 4 :* x) :+ x))
      :=
      con 15 :* x)
    refl (Power.powNat n 3)

degreeFourSuccessorEnvelope :
  ∀ n → 1 ≤ n →
  Power.powNat (suc n) 4
    ≤ Power.powNat n 4 + 15 * Power.powNat n 3
degreeFourSuccessorEnvelope n nPositive =
  let
    p0≤p1 =
      powerSuccessorMonotone nPositive 0
    p1≤p2 =
      powerSuccessorMonotone nPositive 1
    p2≤p3 =
      powerSuccessorMonotone nPositive 2

    p0≤p3 =
      NatP.≤-trans p0≤p1
        (NatP.≤-trans p1≤p2 p2≤p3)
    p1≤p3 =
      NatP.≤-trans p1≤p2 p2≤p3

    sixP2≤sixP3 =
      NatP.*-mono-≤ NatP.≤-refl p2≤p3
    fourP1≤fourP3 =
      NatP.*-mono-≤ NatP.≤-refl p1≤p3

    tailBound =
      NatP.+-mono-≤ NatP.≤-refl
        (NatP.+-mono-≤ sixP2≤sixP3
          (NatP.+-mono-≤ fourP1≤fourP3 p0≤p3))

    expandedBound =
      NatP.+-mono-≤ NatP.≤-refl tailBound
  in
  NatP.≤-trans
    (NatP.≤-reflexive (degreeFourExpansion n))
    (NatP.≤-trans
      expandedBound
      (NatP.≤-reflexive
        (degreeFourTailCollapse n)))

degreeSixExpansion :
  ∀ n →
  Power.powNat (suc n) 6
  ≡
  Power.powNat n 6
    + (6 * Power.powNat n 5
    + (15 * Power.powNat n 4
    + (20 * Power.powNat n 3
    + (15 * Power.powNat n 2
    + (6 * Power.powNat n 1
    + Power.powNat n 0)))))
degreeSixExpansion n =
  solve 1
    (λ x →
      ((con 1 :+ x) :* ((con 1 :+ x) :*
        ((con 1 :+ x) :* ((con 1 :+ x) :*
          ((con 1 :+ x) :* ((con 1 :+ x) :* con 1))))))
      :=
      (x :* (x :* (x :* (x :* (x :* (x :* con 1))))))
        :+
        ((con 6 :* (x :* (x :* (x :* (x :* (x :* con 1))))))
          :+
          ((con 15 :* (x :* (x :* (x :* (x :* con 1)))))
            :+
            ((con 20 :* (x :* (x :* (x :* con 1))))
              :+
              ((con 15 :* (x :* (x :* con 1)))
                :+
                ((con 6 :* (x :* con 1)) :+ con 1))))))
    refl n

degreeSixTailCollapse :
  ∀ n →
  6 * Power.powNat n 5
    + (15 * Power.powNat n 5
    + (20 * Power.powNat n 5
    + (15 * Power.powNat n 5
    + (6 * Power.powNat n 5
    + Power.powNat n 5))))
  ≡
  63 * Power.powNat n 5
degreeSixTailCollapse n =
  solve 1
    (λ x →
      (con 6 :* x)
        :+ ((con 15 :* x)
          :+ ((con 20 :* x)
            :+ ((con 15 :* x)
              :+ ((con 6 :* x) :+ x))))
      :=
      con 63 :* x)
    refl (Power.powNat n 5)

degreeSixSuccessorEnvelope :
  ∀ n → 1 ≤ n →
  Power.powNat (suc n) 6
    ≤ Power.powNat n 6 + 63 * Power.powNat n 5
degreeSixSuccessorEnvelope n nPositive =
  let
    p0≤p1 = powerSuccessorMonotone nPositive 0
    p1≤p2 = powerSuccessorMonotone nPositive 1
    p2≤p3 = powerSuccessorMonotone nPositive 2
    p3≤p4 = powerSuccessorMonotone nPositive 3
    p4≤p5 = powerSuccessorMonotone nPositive 4

    p0≤p5 =
      NatP.≤-trans p0≤p1
        (NatP.≤-trans p1≤p2
          (NatP.≤-trans p2≤p3
            (NatP.≤-trans p3≤p4 p4≤p5)))
    p1≤p5 =
      NatP.≤-trans p1≤p2
        (NatP.≤-trans p2≤p3
          (NatP.≤-trans p3≤p4 p4≤p5))
    p2≤p5 =
      NatP.≤-trans p2≤p3
        (NatP.≤-trans p3≤p4 p4≤p5)
    p3≤p5 =
      NatP.≤-trans p3≤p4 p4≤p5

    fifteenP4≤fifteenP5 =
      NatP.*-mono-≤ NatP.≤-refl p4≤p5
    twentyP3≤twentyP5 =
      NatP.*-mono-≤ NatP.≤-refl p3≤p5
    fifteenP2≤fifteenP5 =
      NatP.*-mono-≤ NatP.≤-refl p2≤p5
    sixP1≤sixP5 =
      NatP.*-mono-≤ NatP.≤-refl p1≤p5

    tailBound =
      NatP.+-mono-≤ NatP.≤-refl
        (NatP.+-mono-≤ fifteenP4≤fifteenP5
          (NatP.+-mono-≤ twentyP3≤twentyP5
            (NatP.+-mono-≤ fifteenP2≤fifteenP5
              (NatP.+-mono-≤ sixP1≤sixP5 p0≤p5))))

    expandedBound =
      NatP.+-mono-≤ NatP.≤-refl tailBound
  in
  NatP.≤-trans
    (NatP.≤-reflexive (degreeSixExpansion n))
    (NatP.≤-trans
      expandedBound
      (NatP.≤-reflexive
        (degreeSixTailCollapse n)))
