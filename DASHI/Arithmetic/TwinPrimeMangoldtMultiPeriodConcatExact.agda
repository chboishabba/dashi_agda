module DASHI.Arithmetic.TwinPrimeMangoldtMultiPeriodConcatExact where

------------------------------------------------------------------------
-- M13: ARBITRARY MANY COMPLETE 270-ROWS, ORDER-PRESERVING BIDI.
-- Reuse DASHI's finite sum and exact Fin270 contiguous row owners.
-- The algebraic boundary is explicit: LEFT IDENTITY and ASSOCIATIVITY.
-- No scalar positivity, commutativity, Archimedean order, prime
-- distribution, or Monster same-object identification is assumed.
-- Source-written, Agda kernel pending, 29 October 2026.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Data.Nat.Properties as NP
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtFinIntervalReindexExact as Row

record MonoidSum (S : Sum.AdditiveScalar) : Set₁ where
  field
    leftIdentity : (x : Sum.Scalar S) → Sum.add S (Sum.zero S) x ≡ x
    associative : (x y z : Sum.Scalar S) →
      Sum.add S (Sum.add S x y) z
      ≡ Sum.add S x (Sum.add S y z)
open MonoidSum

-- Split an ordered contiguous finite fold without rearranging terms.
sumIntervalSplit :
  (S : Sum.AdditiveScalar) (M : MonoidSum S)
  (f : Nat → Sum.Scalar S) (start countLeft countRight : Nat) →
  Sum.add S
    (Sum.sumInterval S f start countLeft)
    (Sum.sumInterval S f (start + countLeft) countRight)
  ≡ Sum.sumInterval S f start (countLeft + countRight)
sumIntervalSplit S M f start zero countRight =
  leftIdentity M (Sum.sumInterval S f start countRight)
sumIntervalSplit S M f start (suc countLeft) countRight
  rewrite NP.+-suc start countLeft =
  trans
    (associative M
      (f start)
      (Sum.sumInterval S f (suc start) countLeft)
      (Sum.sumInterval S f (suc start + countLeft) countRight))
    (cong (Sum.add S (f start))
      (sumIntervalSplit S M f (suc start) countLeft countRight))

-- Same arithmetic index sequence as one ordered contiguous interval.
-- This is an induction over arbitrary row counts, not finite enumeration.
blockRows : (S : Sum.AdditiveScalar) (f : Nat → Sum.Scalar S)
  (start rows : Nat) → Sum.Scalar S
blockRows S f start zero = Sum.zero S
blockRows S f start (suc rows) =
  Sum.add S
    (Sum.sumInterval S f start 270)
    (blockRows S f (start + 270) rows)

blockRowsCorrect :
  (S : Sum.AdditiveScalar) (M : MonoidSum S)
  (f : Nat → Sum.Scalar S) (start rows : Nat) →
  blockRows S f start rows
    ≡ Sum.sumInterval S f start (rows * 270)
blockRowsCorrect S M f start zero = refl
blockRowsCorrect S M f start (suc rows) =
  trans
    (cong
      (Sum.add S (Sum.sumInterval S f start 270))
      (blockRowsCorrect S M f (start + 270) rows))
    (sumIntervalSplit S M f start 270 (rows * 270))

-- The source-preserving BIDI for any number of complete period rows:
-- start index must be aligned to the period boundary.
codeBlockRows : (S : Sum.AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (startPeriod rows : Nat) → Sum.Scalar S
codeBlockRows S C startPeriod zero = Sum.zero S
codeBlockRows S C startPeriod (suc rows) =
  Sum.add S
    (Sum.sumDecodedInterval S
      (Bidi.pairCorrelationAtPeriod C) (startPeriod * 270) 270)
    (codeBlockRows S C (suc startPeriod) rows)

-- Use original pointwise BIDI in each row. The only indexing
-- arithmetic used for the next start is (suc k)*270= k*270+270;
-- Nat addition commutativity is allowed, scalar commutativity is NOT.

------------------------------------------------------------------------
-- M13 block BIDI closure: all period counts, both directions.
--
-- The sole conversion between (suc k)*270 and k*270+270 is
-- elementary Nat arithmetic (commutativity); there is still NO
-- reordering of Scalar terms.
------------------------------------------------------------------------

codeBlockRowsCorrect :
  (S : Sum.AdditiveScalar) (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (startPeriod rows : Nat) →
  codeBlockRows S C startPeriod rows
    ≡ blockRows S (Bidi.pairCorrelationAtNat C)
        (startPeriod * 270) rows
codeBlockRowsCorrect S C startPeriod zero = refl
codeBlockRowsCorrect S C startPeriod (suc rows) =
  cong₂ (Sum.add S)
    (Sum.pairFiniteSumBidiForward S C (startPeriod * 270) 270)
    (trans
      (codeBlockRowsCorrect S C (suc startPeriod) rows)
      (cong
        (λ start → blockRows S (Bidi.pairCorrelationAtNat C) start rows)
        (NP.+-comm 270 (startPeriod * 270))))

codeBlockRowsToInterval :
  (S : Sum.AdditiveScalar) (M : MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (startPeriod rows : Nat) →
  codeBlockRows S C startPeriod rows
    ≡ Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
        (startPeriod * 270) (rows * 270)
codeBlockRowsToInterval S M C startPeriod rows =
  trans
    (codeBlockRowsCorrect S C startPeriod rows)
    (blockRowsCorrect S M (Bidi.pairCorrelationAtNat C)
      (startPeriod * 270) rows)

intervalToCodeBlockRows :
  (S : Sum.AdditiveScalar) (M : MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S))
  (startPeriod rows : Nat) →
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
      (startPeriod * 270) (rows * 270)
    ≡ codeBlockRows S C startPeriod rows
intervalToCodeBlockRows S M C startPeriod rows =
  sym (codeBlockRowsToInterval S M C startPeriod rows)
