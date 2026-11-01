module DASHI.Physics.Closure.NSTriadKNCompactTransferPotentialBoundedRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / BOUNDED COMPACT-TRANSFER POTENTIAL
--
-- On the resolved positive-transfer branch write
--
--   Q >= 0,
--   V = 2 nu D >= 0,
--   Q + V > 0,
--   B = Q / (Q + V).
--
-- This file proves directly over exact rationals that
--
--   0 <= B <= 1.
--
-- Division is represented explicitly as multiplication by the reciprocal of
-- the positive denominator so every positivity/nonzero obligation is visible.
-- The proof is independent of any drift/coercivity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; 1/_; Positive; NonNegative; NonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

positiveReciprocal : (denominator : ℚ) → 0ℚ < denominator → ℚ
positiveReciprocal denominator denominatorPositive =
  let
    instance
      denominatorPos : Positive denominator
      denominatorPos = ℚ.positive denominatorPositive
      denominatorNZ : NonZero denominator
      denominatorNZ = ℚP.pos⇒nonZero denominator
  in
  1/ denominator

positiveReciprocalRightInverse :
  ∀ denominator (denominatorPositive : 0ℚ < denominator) →
  denominator * positiveReciprocal denominator denominatorPositive ≡ 1ℚ
positiveReciprocalRightInverse denominator denominatorPositive =
  let
    instance
      denominatorPos : Positive denominator
      denominatorPos = ℚ.positive denominatorPositive
      denominatorNZ : NonZero denominator
      denominatorNZ = ℚP.pos⇒nonZero denominator
  in
  ℚP.*-inverseʳ denominator

positiveReciprocalNonnegative :
  ∀ denominator (denominatorPositive : 0ℚ < denominator) →
  0ℚ ≤ positiveReciprocal denominator denominatorPositive
positiveReciprocalNonnegative denominator denominatorPositive =
  let
    instance
      denominatorPos : Positive denominator
      denominatorPos = ℚ.positive denominatorPositive
      denominatorNZ : NonZero denominator
      denominatorNZ = ℚP.pos⇒nonZero denominator
      reciprocalPos : Positive (1/ denominator)
      reciprocalPos = ℚP.1/pos⇒pos denominator
  in
  ℚP.<⇒≤ (ℚP.positive⁻¹ (1/ denominator))

compactTransferPotential :
  (Q V : ℚ) → 0ℚ < Q + V → ℚ
compactTransferPotential Q V denominatorPositive =
  Q * positiveReciprocal (Q + V) denominatorPositive

record PositiveCompactTransferDatum : Set where
  constructor positive-compact-transfer
  field
    transfer viscous : ℚ
    transferNonnegative : 0ℚ ≤ transfer
    viscousNonnegative : 0ℚ ≤ viscous
    denominatorPositive : 0ℚ < transfer + viscous

open PositiveCompactTransferDatum public

compactPotential : PositiveCompactTransferDatum → ℚ
compactPotential datum =
  compactTransferPotential
    (transfer datum) (viscous datum) (denominatorPositive datum)

compactPotentialNonnegative :
  (datum : PositiveCompactTransferDatum) →
  0ℚ ≤ compactPotential datum
compactPotentialNonnegative datum =
  let
    reciprocalNN = positiveReciprocalNonnegative
      (transfer datum + viscous datum) (denominatorPositive datum)
    instance
      qNN : NonNegative (transfer datum)
      qNN = ℚ.nonNegative (transferNonnegative datum)
      rNN : NonNegative
        (positiveReciprocal
          (transfer datum + viscous datum) (denominatorPositive datum))
      rNN = ℚ.nonNegative reciprocalNN
  in
  ℚP.nonNegative⁻¹ (compactPotential datum)

transferBelowDenominator :
  (datum : PositiveCompactTransferDatum) →
  transfer datum ≤ transfer datum + viscous datum
transferBelowDenominator datum =
  subst
    (λ left → left ≤ transfer datum + viscous datum)
    (ℚP.+-identityʳ (transfer datum))
    (ℚP.+-mono-≤
      (ℚP.≤-refl {x = transfer datum})
      (viscousNonnegative datum))

compactPotentialBelowOne :
  (datum : PositiveCompactTransferDatum) →
  compactPotential datum ≤ 1ℚ
compactPotentialBelowOne datum =
  let
    reciprocal = positiveReciprocal
      (transfer datum + viscous datum) (denominatorPositive datum)
    reciprocalNNProof = positiveReciprocalNonnegative
      (transfer datum + viscous datum) (denominatorPositive datum)
    instance
      reciprocalNN : NonNegative reciprocal
      reciprocalNN = ℚ.nonNegative reciprocalNNProof

    scaled :
      transfer datum * reciprocal
      ≤ (transfer datum + viscous datum) * reciprocal
    scaled = ℚP.*-monoʳ-≤-nonNeg reciprocal (transferBelowDenominator datum)

    endpoint :
      (transfer datum + viscous datum) * reciprocal ≡ 1ℚ
    endpoint = positiveReciprocalRightInverse
      (transfer datum + viscous datum) (denominatorPositive datum)
  in
  subst
    (λ upper → compactPotential datum ≤ upper)
    endpoint
    scaled

round82CompactTransferPotentialBoundedZeroOne : Bool
round82CompactTransferPotentialBoundedZeroOne = true

round82CompactTransferPotentialBoundedZeroOneIsTrue :
  round82CompactTransferPotentialBoundedZeroOne ≡ true
round82CompactTransferPotentialBoundedZeroOneIsTrue = refl
