module DASHI.Arithmetic.TwinPrimeResidualMangoldtPeriodRowsExact where

------------------------------------------------------------------------
-- FINITE PERIOD ROWS, ACTUAL FIN270 INDICES
-- Reuses the original Nat <-> period/residue full BIDI, and the
-- existing finite-sum / Mangoldt correlation consumer owner.
-- One row contains ALL 270 residue positions, including rejected
-- ones. Surviving 27 residues are not confused with all Nats.
-- This is the rowwise part of M13, not its arbitrary-interval
-- reindexing theorem; no analytic estimate, kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base as Fin using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym)

import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum

-- Each period row is indexed by a genuine bounded residue.
rowNat : Nat → Fin 270 → Nat
rowNat period residue =
  Period.decodeNatPeriod270 (Period.natPeriod270 period residue)

rowEncodeDecode : (period : Nat) (r : Fin 270) →
  Period.encodeNatPeriod270 (rowNat period r)
    ≡ Period.natPeriod270 period r
rowEncodeDecode period r =
  Period.encodeDecodeNatPeriod270
    (Period.natPeriod270 period r)

rowConsumerForward : {A : Set} (consumer : Nat → A) →
  (period : Nat) (r : Fin 270) →
  Bidi.liftNatConsumer consumer
    (Period.encodeNatPeriod270 (rowNat period r))
    ≡ consumer (rowNat period r)
rowConsumerForward consumer period r =
  Bidi.liftConsumerSound consumer (rowNat period r)

rowConsumerBackward : {A : Set} (consumer : Nat → A) →
  (period : Nat) (r : Fin 270) →
  consumer (rowNat period r) ≡
  Bidi.liftNatConsumer consumer (Period.natPeriod270 period r)
rowConsumerBackward consumer period r = refl

-- A closed finite sum over every Fin m index, independent of the
-- order on the algebraic Scalar. Use this one explicit ascending
-- enumeration; no subtraction and no modular wraparound.
sumFinFrom : (S : Sum.AdditiveScalar) →
  (m : Nat) → (Fin m → Sum.Scalar S) → Sum.Scalar S
sumFinFrom S zero f = Sum.zero S
sumFinFrom S (suc m) f =
  Sum.add S (f Fin.zero)
    (sumFinFrom S m (λ r → f (Fin.suc r)))

periodRowSum : (S : Sum.AdditiveScalar)
  (f : Nat → Sum.Scalar S) → Nat → Sum.Scalar S
periodRowSum S f period =
  sumFinFrom S 270 (λ r → f (rowNat period r))

periodRowCodeSum : (S : Sum.AdditiveScalar)
  (f : Period.NatPeriod270 → Sum.Scalar S) →
  Nat → Sum.Scalar S
periodRowCodeSum S f period =
  sumFinFrom S 270
    (λ r → f (Period.natPeriod270 period r))

sumFinCongruence : (S : Sum.AdditiveScalar) (m : Nat)
  {f g : Fin m → Sum.Scalar S} →
  ((r : Fin m) → f r ≡ g r) →
  sumFinFrom S m f ≡ sumFinFrom S m g
sumFinCongruence S zero equal = refl
sumFinCongruence S (suc m) equal =
  cong₂ (Sum.add S)
    (equal Fin.zero)
    (sumFinCongruence S m (λ r → equal (Fin.suc r)))

periodRowBidiForward :
  (S : Sum.AdditiveScalar) (f : Nat → Sum.Scalar S)
  (period : Nat) →
  periodRowCodeSum S (Bidi.liftNatConsumer f) period
    ≡ periodRowSum S f period
periodRowBidiForward S f period =
  sumFinCongruence S 270
    (λ r → sym (rowConsumerBackward f period r))

periodRowBidiBackward :
  (S : Sum.AdditiveScalar) (f : Nat → Sum.Scalar S)
  (period : Nat) →
  periodRowSum S f period
    ≡ periodRowCodeSum S (Bidi.liftNatConsumer f) period
periodRowBidiBackward S f period =
  sym (periodRowBidiForward S f period)

periodPairCorrelationBidi :
  (S : Sum.AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (period : Nat) →
  periodRowCodeSum S (Bidi.pairCorrelationAtPeriod C) period
    ≡ periodRowSum S (Bidi.pairCorrelationAtNat C) period
periodPairCorrelationBidi S C period =
  periodRowBidiForward S (Bidi.pairCorrelationAtNat C) period
