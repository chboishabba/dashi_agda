module DASHI.Physics.Chemistry.Atomic369Kernel6HeisenbergBridgeExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec; []; _∷_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

------------------------------------------------------------------------
-- ATOMIC 369 DEPTH-SIX KERNEL <-> MONSTER HEISENBERG POSITION CARRIER
--
-- AtomicPeriodicTable369GenerativeExact reuses Triadic.Kernel d as its ternary
-- substrate.  Monster3BFiniteHeisenbergGeneratorsExact uses X6 = F3^6.  At
-- depth six the two finite carriers are exactly coordinatewise isomorphic.
--
-- This is a structural same-carrier chart.  It does not assign a physical NH3
-- electronic state to a particular kernel point, nor does it create a Monster
-- action or any physical same-object authority.
------------------------------------------------------------------------

Kernel6 : Set
Kernel6 = Atomic369.TernaryKernel 6

HeisenbergX6 : Set
HeisenbergX6 = H.X6

kernelTritToTrit : Triadic.KernelTrit → Trit
kernelTritToTrit Triadic.negativeTrit = neg
kernelTritToTrit Triadic.zeroTrit = zer
kernelTritToTrit Triadic.positiveTrit = pos

tritToKernelTrit : Trit → Triadic.KernelTrit
tritToKernelTrit neg = Triadic.negativeTrit
tritToKernelTrit zer = Triadic.zeroTrit
tritToKernelTrit pos = Triadic.positiveTrit

kernelTritRoundTrip :
  (t : Triadic.KernelTrit) → tritToKernelTrit (kernelTritToTrit t) ≡ t
kernelTritRoundTrip Triadic.negativeTrit = refl
kernelTritRoundTrip Triadic.zeroTrit = refl
kernelTritRoundTrip Triadic.positiveTrit = refl

tritRoundTrip : (t : Trit) → kernelTritToTrit (tritToKernelTrit t) ≡ t
tritRoundTrip neg = refl
tritRoundTrip zer = refl
tritRoundTrip pos = refl

kernel6ToX6 : Kernel6 → HeisenbergX6
kernel6ToX6 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []) =
  H.x6
    (kernelTritToTrit a)
    (kernelTritToTrit b)
    (kernelTritToTrit c)
    (kernelTritToTrit d)
    (kernelTritToTrit e)
    (kernelTritToTrit f)

x6ToKernel6 : HeisenbergX6 → Kernel6
x6ToKernel6 x =
  tritToKernelTrit (H.x0 x) ∷
  tritToKernelTrit (H.x1 x) ∷
  tritToKernelTrit (H.x2 x) ∷
  tritToKernelTrit (H.x3 x) ∷
  tritToKernelTrit (H.x4 x) ∷
  tritToKernelTrit (H.x5 x) ∷ []

kernel6RoundTrip : (k : Kernel6) → x6ToKernel6 (kernel6ToX6 k) ≡ k
kernel6RoundTrip (Triadic.negativeTrit ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
  rewrite kernelTritRoundTrip b | kernelTritRoundTrip c | kernelTritRoundTrip d
        | kernelTritRoundTrip e | kernelTritRoundTrip f = refl
kernel6RoundTrip (Triadic.zeroTrit ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
  rewrite kernelTritRoundTrip b | kernelTritRoundTrip c | kernelTritRoundTrip d
        | kernelTritRoundTrip e | kernelTritRoundTrip f = refl
kernel6RoundTrip (Triadic.positiveTrit ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])
  rewrite kernelTritRoundTrip b | kernelTritRoundTrip c | kernelTritRoundTrip d
        | kernelTritRoundTrip e | kernelTritRoundTrip f = refl

x6RoundTrip : (x : HeisenbergX6) → kernel6ToX6 (x6ToKernel6 x) ≡ x
x6RoundTrip (H.x6 neg b c d e f)
  rewrite tritRoundTrip b | tritRoundTrip c | tritRoundTrip d
        | tritRoundTrip e | tritRoundTrip f = refl
x6RoundTrip (H.x6 zer b c d e f)
  rewrite tritRoundTrip b | tritRoundTrip c | tritRoundTrip d
        | tritRoundTrip e | tritRoundTrip f = refl
x6RoundTrip (H.x6 pos b c d e f)
  rewrite tritRoundTrip b | tritRoundTrip c | tritRoundTrip d
        | tritRoundTrip e | tritRoundTrip f = refl

record Kernel6HeisenbergIsomorphism : Set where
  constructor kernel6HeisenbergIsomorphism
  field
    forward : Kernel6 → HeisenbergX6
    backward : HeisenbergX6 → Kernel6
    backwardForward : (k : Kernel6) → backward (forward k) ≡ k
    forwardBackward : (x : HeisenbergX6) → forward (backward x) ≡ x

canonicalKernel6HeisenbergIsomorphism : Kernel6HeisenbergIsomorphism
canonicalKernel6HeisenbergIsomorphism =
  kernel6HeisenbergIsomorphism kernel6ToX6 x6ToKernel6 kernel6RoundTrip x6RoundTrip

record Kernel6HeisenbergBoundary : Set where
  constructor kernel6HeisenbergBoundary
  field
    atomic369UsesTriadicKernel : Bool
    atomic369UsesTriadicKernelIsTrue : atomic369UsesTriadicKernel ≡ true
    kernel6HeisenbergCarrierIsomorphismPaid : Bool
    kernel6HeisenbergCarrierIsomorphismPaidIsTrue :
      kernel6HeisenbergCarrierIsomorphismPaid ≡ true
    physicalNH3StateToKernel6AssignmentPaid : Bool
    physicalNH3StateToKernel6AssignmentPaidIsFalse :
      physicalNH3StateToKernel6AssignmentPaid ≡ false
    carrierIsomorphismCreatesMonsterAction : Bool
    carrierIsomorphismCreatesMonsterActionIsFalse :
      carrierIsomorphismCreatesMonsterAction ≡ false
    interpretation : String

open Kernel6HeisenbergBoundary public

canonicalKernel6HeisenbergBoundary : Kernel6HeisenbergBoundary
canonicalKernel6HeisenbergBoundary =
  kernel6HeisenbergBoundary
    true refl
    true refl
    false refl
    false refl
    "Atomic 369 Kernel 6 and Monster Heisenberg X6 are exact coordinate carriers. The remaining chemistry payment is a physically justified NH3-state -> Kernel6 assignment, not a carrier-construction problem."
