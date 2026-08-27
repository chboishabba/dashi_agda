module DASHI.Physics.Closure.NSTriadKNExternalHHSquareGapGramRound128Exact where

------------------------------------------------------------------------
-- ROUND128 / DIVISION-FREE HH SQUARE-GAP GRAM CONTROL
--
-- Round125 exposed
--
--     Delta_2 := |q|^2 - |p|^2 = k . (q-p).
--
-- The next high-alpha step does not need square roots.  Apply the already
-- machine-checked Plucker/Gram identity to the pair
--
--     k , d := q-p.
--
-- This yields an EXACT Cauchy identity with an explicit nonnegative geometric
-- remainder once transported to an ordered carrier:
--
--     Delta_2^2 + |k x d|^2 = |k|^2 |d|^2.
--
-- Resonance also gives the exact parallelogram identity
--
--     |d|^2 + |k|^2 = 2|p|^2 + 2|q|^2.
--
-- Hence
--
--     Delta_2^2 + |k x (q-p)|^2
--       = |k|^2 (2|p|^2 + 2|q|^2 - |k|^2).
--
-- Everything here is integer polynomial algebra.  In the ordered-real layer,
-- dropping the Plucker square immediately gives the desired low-output-times-
-- high-input control of the SQUARED radial numerator, still without any
-- convolution-cardinality factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _-_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadPluckerInvariantRound27Exact as Plane
import DASHI.Physics.Closure.NSTriadKNExternalHHEuclideanSquareGapFactorRound125Exact as R125

module RingZ = NR IntRS.ring

two : ℤ
two = + 2

differenceMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
differenceMode q p = R125.subtractMode q p

parallelogramForSumDifference :
  ∀ p q →
  Plane.modeNormSquared (differenceMode q p)
    + Plane.modeNormSquared (Z3.addMode p q)
  ≡
  two * Plane.modeNormSquared p
    + two * Plane.modeNormSquared q
parallelogramForSumDifference
    (Z3.mode px py pz) (Z3.mode qx qy qz) =
  RingZ.solve 6
    (λ px py pz qx qy qz →
      ( ((qx - px) * (qx - px)
          + (qy - py) * (qy - py)
          + (qz - pz) * (qz - pz))
        + ((px + qx) * (px + qx)
          + (py + qy) * (py + qy)
          + (pz + qz) * (pz + qz))
      , (+ 2) * (px * px + py * py + pz * pz)
          + (+ 2) * (qx * qx + qy * qy + qz * qz)))
    refl px py pz qx qy qz

resonantParallelogram :
  (tau : Physical.PhysicalTriadIncidence) →
  Plane.modeNormSquared
      (differenceMode (Physical.q tau) (Physical.p tau))
    + Plane.modeNormSquared (Physical.k tau)
  ≡
  two * Plane.modeNormSquared (Physical.p tau)
    + two * Plane.modeNormSquared (Physical.q tau)
resonantParallelogram tau =
  subst
    (λ output →
      Plane.modeNormSquared
          (differenceMode (Physical.q tau) (Physical.p tau))
        + Plane.modeNormSquared output
      ≡
      two * Plane.modeNormSquared (Physical.p tau)
        + two * Plane.modeNormSquared (Physical.q tau))
    (Physical.resonance tau)
    (parallelogramForSumDifference (Physical.p tau) (Physical.q tau))

-- Rearranged Gram determinant identity.  The Plucker term is retained rather
-- than discarded, so this theorem needs no order structure.
gramCauchyIdentity :
  ∀ k d →
  Plane.dotMode k d * Plane.dotMode k d
    + Plane.pluckerNormSquared k d
  ≡ Plane.modeNormSquared k * Plane.modeNormSquared d
gramCauchyIdentity k d =
  trans
    (congLeft (Plane.pluckerGramIdentity k d))
    (RingZ.solve 3
      (λ dot nk nd →
        (dot * dot + (nk * nd - dot * dot)
        , nk * nd))
      refl
      (Plane.dotMode k d)
      (Plane.modeNormSquared k)
      (Plane.modeNormSquared d))
  where
  congLeft :
    Plane.pluckerNormSquared k d
      ≡ Plane.modeNormSquared k * Plane.modeNormSquared d
        - Plane.dotMode k d * Plane.dotMode k d →
    Plane.dotMode k d * Plane.dotMode k d
      + Plane.pluckerNormSquared k d
      ≡
    Plane.dotMode k d * Plane.dotMode k d
      + (Plane.modeNormSquared k * Plane.modeNormSquared d
        - Plane.dotMode k d * Plane.dotMode k d)
  congLeft refl = refl

squareGapGramIdentity :
  (tau : Physical.PhysicalTriadIncidence) →
  let d = differenceMode (Physical.q tau) (Physical.p tau)
      delta = R125.squareGap (Physical.p tau) (Physical.q tau)
  in
  delta * delta + Plane.pluckerNormSquared (Physical.k tau) d
  ≡ Plane.modeNormSquared (Physical.k tau) * Plane.modeNormSquared d
squareGapGramIdentity tau =
  let
    d = differenceMode (Physical.q tau) (Physical.p tau)
    factor = R125.resonantSquareGapFactorsThroughOutput tau
  in
  subst
    (λ delta →
      delta * delta + Plane.pluckerNormSquared (Physical.k tau) d
      ≡ Plane.modeNormSquared (Physical.k tau) * Plane.modeNormSquared d)
    (sym factor)
    (gramCauchyIdentity (Physical.k tau) d)
  where
  open import Relation.Binary.PropositionalEquality using (sym)

-- Fully eliminated d-norm.  This is the exact polynomial numerator identity
-- that the ordered-real HH estimate should consume.
hhSquareGapLowHighIdentity :
  (tau : Physical.PhysicalTriadIncidence) →
  let d = differenceMode (Physical.q tau) (Physical.p tau)
      delta = R125.squareGap (Physical.p tau) (Physical.q tau)
      nk = Plane.modeNormSquared (Physical.k tau)
      np = Plane.modeNormSquared (Physical.p tau)
      nq = Plane.modeNormSquared (Physical.q tau)
  in
  delta * delta + Plane.pluckerNormSquared (Physical.k tau) d
  ≡ nk * (two * np + two * nq - nk)
hhSquareGapLowHighIdentity tau =
  let
    d = differenceMode (Physical.q tau) (Physical.p tau)
    nk = Plane.modeNormSquared (Physical.k tau)
    np = Plane.modeNormSquared (Physical.p tau)
    nq = Plane.modeNormSquared (Physical.q tau)
    gram = squareGapGramIdentity tau
    para = resonantParallelogram tau
    dNormMeaning : Plane.modeNormSquared d ≡ two * np + two * nq - nk
    dNormMeaning =
      RingZ.solve 4
        (λ nd nk rhs →
          (nd + nk , rhs) →
          (nd , rhs - nk))
        para
        (Plane.modeNormSquared d)
        nk
        (two * np + two * nq)
  in
  subst
    (λ dNorm →
      R125.squareGap (Physical.p tau) (Physical.q tau)
        * R125.squareGap (Physical.p tau) (Physical.q tau)
        + Plane.pluckerNormSquared (Physical.k tau) d
      ≡ nk * dNorm)
    dNormMeaning
    gram

round128ParallelogramIdentityClosed : Bool
round128ParallelogramIdentityClosed = true

round128SquareGapGramIdentityClosed : Bool
round128SquareGapGramIdentityClosed = true

round128LowOutputTimesHighInputPolynomialIdentityClosed : Bool
round128LowOutputTimesHighInputPolynomialIdentityClosed = true

round128OrderedDropPluckerRemainderClosed : Bool
round128OrderedDropPluckerRemainderClosed = false

round128CriticalHHPaymentClosed : Bool
round128CriticalHHPaymentClosed = false

round128LowOutputTimesHighInputPolynomialIdentityClosedIsTrue :
  round128LowOutputTimesHighInputPolynomialIdentityClosed ≡ true
round128LowOutputTimesHighInputPolynomialIdentityClosedIsTrue = refl

round128OrderedDropPluckerRemainderClosedIsFalse :
  round128OrderedDropPluckerRemainderClosed ≡ false
round128OrderedDropPluckerRemainderClosedIsFalse = refl

round128CriticalHHPaymentClosedIsFalse :
  round128CriticalHHPaymentClosed ≡ false
round128CriticalHHPaymentClosedIsFalse = refl
