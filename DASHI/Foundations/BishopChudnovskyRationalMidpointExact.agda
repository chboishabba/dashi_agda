module DASHI.Foundations.BishopChudnovskyRationalMidpointExact where

-- Source-written; not kernel checked. Reference evaluator, not fast GMP.
-- Use the original raw split node, the original integer sqrt owner and
-- the original unnormalised rational carrier. No fabricated midpoint
-- when a denominator or positivity check fails.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (ℤ; +_; -_)
open import Data.Nat using (_^_)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; _+_; _*_)

import DASHI.Foundations.HypergeometricBSplitIntegerMergeExact as Split
import DASHI.Foundations.BishopNatSquareRootFloorApproximationExact as Root

A B C : Nat
A = 13591409
B = 545140134
C = 640320 ^ 3

-- At j=suc i, the factors 2j-1,6j-5,6j-1 are expressed
-- as positive naturals, not truncated signed subtractions.
sourceP : Nat → ℤ
sourceP zero = + 1
sourceP (suc i) =
  - (+ (24 * (2 * i + 1) * (6 * i + 1) * (6 * i + 5)))

sourceQ : Nat → ℤ
sourceQ zero = + 1
sourceQ (suc i) = + (C * (suc i ^ 3))

sourceLeaf : Nat → Split.SplitNode
sourceLeaf j = Split.leaf (+ (A + B * j)) (+ 1) (sourceP j) (sourceQ j)

-- Literal ordered prefix; regrouping uses the existing merge theorem.
-- Deliberately not a performance substitute for balanced native GMP.
sourcePrefix : Nat → Split.SplitNode
sourcePrefix zero = Split.empty
sourcePrefix (suc j) = Split.merge (sourcePrefix j) (sourceLeaf j)

-- ceil((k+5)/41) = 1+floor((k+4)/41) for k>=0.
cutoff : Nat → Nat
cutoff k = suc ((k + 4) ND./ 41)

rootBits rootScale rootNumerator : Nat → Nat
rootBits k = k + 2
rootScale k = 2 ^ rootBits k
rootNumerator k = Root.floorSquareRootNumerator 10005 (rootScale k)

rootLowerSquare : (k : Nat) →
  N._≤_ (rootNumerator k * rootNumerator k)
    (Root.scaledSquareTarget 10005 (rootScale k))
rootLowerSquare k =
  Root.floorNumeratorSquareBelowScaledTarget 10005 (rootScale k)

rootUpperSquare : (k : Nat) →
  N._≤_ (Root.scaledSquareTarget 10005 (rootScale k))
    (suc (rootNumerator k) * suc (rootNumerator k))
rootUpperSquare k =
  Root.scaledTargetBelowSuccessorNumeratorSquare 10005 (rootScale k)

-- Positive series sum T/(Q*B). Predecessors encode positivity
-- without relying on a caller-provided arbitrary denominator.
record PositiveSum : Set where
  constructor positiveSum
  field
    numeratorPred denominatorPred : Nat
open PositiveSum

positiveView : Split.SplitNode → Maybe PositiveSum
positiveView s with Split.T s | Split.Q s | Split.B s
... | (+ (suc t)) | (+ (suc q)) | (+ (suc b)) =
  just (positiveSum t (q * suc b + b))
... | _ | _ | _ = nothing
-- suc(q * suc b + b) = (suc q)*(suc b).

num den : PositiveSum → Nat
num s = suc (numeratorPred s)
den s = suc (denominatorPred s)

-- pi endpoint 426880*r/scale / (T/(Q*B)).
endpoint : Nat → Nat → PositiveSum → ℚᵘ
endpoint scalePred r s =
  let
    instance
      denominatorNZ = NP.m*n≢0 (suc scalePred) (num s)
  in
  + (426880 * r * den s) / (suc scalePred * num s)

record Interval : Set where
  constructor interval
  field
    lower upper : ℚᵘ
open Interval

orderedInterval : Nat → Nat → PositiveSum → PositiveSum → Interval
orderedInterval scalePred r x y with
  (num x * den y) NP.≤? (num y * den x)
... | yes _ =
  interval (endpoint scalePred r y) (endpoint scalePred (suc r) x)
... | no _ =
  interval (endpoint scalePred r x) (endpoint scalePred (suc r) y)

intervalAt : Nat → Maybe Interval
intervalAt k with rootScale k | positiveView (sourcePrefix (cutoff k))
                              | positiveView (sourcePrefix (suc (cutoff k)))
... | suc scalePred | just x | just y =
  just (orderedInterval scalePred (rootNumerator k) x y)
... | _ | _ | _ = nothing

midpoint : Interval → ℚᵘ
midpoint w = (+ 1 / 2) Q.* (lower w Q.+ upper w)

midpointAt : Nat → Maybe ℚᵘ
midpointAt k with intervalAt k
... | just w = just (midpoint w)
... | nothing = nothing
