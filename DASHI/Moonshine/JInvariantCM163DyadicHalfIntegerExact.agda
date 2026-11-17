{-# OPTIONS --safe #-}
module DASHI.Moonshine.JInvariantCM163DyadicHalfIntegerExact where

------------------------------------------------------------------------
-- FINITE INTEGER CHECKER: 128-BIT DYADIC CM -163 HALF-INTEGER WINDOW
--
-- Generated source of offsets: exact outward-rounded rational Machin,
-- integer sqrt, exp series and E4/E6 tail bounds in
-- scripts/check_cm163_dyadic_j_integer_certificate.py.
--
-- The two checks below pay only the FINAL integer inequality:
--   -1/2 < -lowerOffset/2^128 <= j-t <= upperOffset/2^128 < 1/2.
-- Supplying the true analytic enclosure for the original Bishop j
-- is a separate, explicit producer obligation. This checker does
-- NOT assert q-series/CM integrality, or manufacture that producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat using (_<_)
import Data.Nat.Properties as NatP
open NatP using (_<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

twoPower128 : Nat
twoPower128 = 340282366920938463463374607431768211456

halfUnit : Nat
halfUnit = 170141183460469231731687303715884105728

lowerOffsetMagnitude : Nat
lowerOffsetMagnitude = 121397398953732472506062368501224644

upperOffsetMagnitude : Nat
upperOffsetMagnitude = 12147930101178244703017603450764613085

twoHalfIsUnit : 2 * halfUnit ≡ twoPower128
twoHalfIsUnit = refl

lowerOffsetLessThanHalf : lowerOffsetMagnitude < halfUnit
lowerOffsetLessThanHalf =
  toWitness {a? = lowerOffsetMagnitude <? halfUnit} _

upperOffsetLessThanHalf : upperOffsetMagnitude < halfUnit
upperOffsetLessThanHalf =
  toWitness {a? = upperOffsetMagnitude <? halfUnit} _

-- The reduced form (a,b,c)=(1,1,41) has discriminant -163:
-- b²+163 = 4ac. Exhaustiveness is an external finite-enumerator
-- receipt until formally linked to the reduced-form classification.

reduced163DiscriminantArithmetic :
  1 * 1 + 163 ≡ 4 * 1 * 41
reduced163DiscriminantArithmetic = refl

------------------------------------------------------------------------
-- This module intentionally does not represent a Hilbert class
-- polynomial or bind the 128-bit interval to an analytic j-value.
-- Additional formal gates:
--   analytic q-series E4/E6 enclosure on the same Bishop complex;
--   class-number-one exhaustion in Agda;
--   CM integrality at the actual quadratic point;
--   classical pi/period identity on original Bishop carrier.
------------------------------------------------------------------------
