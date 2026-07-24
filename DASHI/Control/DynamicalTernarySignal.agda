{-# OPTIONS --safe #-}
module DASHI.Control.DynamicalTernarySignal where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.List using (length)

------------------------------------------------------------------------
-- Exact natural comparison as a balanced trit.
--
-- neg : left < right
-- zer : left = right
-- pos : left > right

compareNat : Nat → Nat → Trit
compareNat zero zero = zer
compareNat zero (suc right) = neg
compareNat (suc left) zero = pos
compareNat (suc left) (suc right) =
  compareNat left right

compareNat-reflexive :
  (n : Nat) →
  compareNat n n ≡ zer
compareNat-reflexive zero = refl
compareNat-reflexive (suc n) =
  compareNat-reflexive n

marginClass : Nat → Nat → Trit
marginClass threshold margin =
  compareNat margin threshold

state-at-threshold :
  (threshold : Nat) →
  marginClass threshold threshold ≡ zer
state-at-threshold threshold =
  compareNat-reflexive threshold

------------------------------------------------------------------------
-- Dynamical ternary signal with an inclusive dead zone.
--
-- A change is rising only when
--
--   after > before + epsilon,
--
-- and falling only when
--
--   before > after + epsilon.
--
-- Everything between those strict inequalities is the genuine stationary
-- state rather than an exact-measure-zero equality case.

trendWithDeadZone : Nat → Nat → Nat → Trit
trendWithDeadZone epsilon before after
  with compareNat (before + epsilon) after
... | neg = pos
... | zer = zer
... | pos with compareNat (after + epsilon) before
...   | neg = neg
...   | zer = zer
...   | pos = zer

rising-example :
  trendWithDeadZone 1 2 4 ≡ pos
rising-example = refl

stationary-upper-edge-example :
  trendWithDeadZone 1 2 3 ≡ zer
stationary-upper-edge-example = refl

stationary-interior-example :
  trendWithDeadZone 2 4 3 ≡ zer
stationary-interior-example = refl

falling-example :
  trendWithDeadZone 1 4 2 ≡ neg
falling-example = refl

zero-dead-zone-reflexive :
  (n : Nat) →
  trendWithDeadZone zero n n ≡ zer
zero-dead-zone-reflexive n
  rewrite +-identityʳ n
        | compareNat-reflexive n = refl

------------------------------------------------------------------------
-- State and velocity are distinct ternary observables.
-- Their product is the literal nine-state local control carrier.

record NonaryControlState : Set where
  constructor control-state
  field
    stateClass : Trit
    motionClass : Trit

open NonaryControlState public

classifyControl :
  Nat →
  Nat →
  Nat →
  Nat →
  NonaryControlState
classifyControl stateThreshold motionDeadZone previous current =
  control-state
    (marginClass stateThreshold current)
    (trendWithDeadZone motionDeadZone previous current)

data AdmissibilityRegime : Set where
  inadmissible marginal admissible : AdmissibilityRegime

data MotionRegime : Set where
  leaving stationary entering : MotionRegime

interpretState : Trit → AdmissibilityRegime
interpretState neg = inadmissible
interpretState zer = marginal
interpretState pos = admissible

interpretMotion : Trit → MotionRegime
interpretMotion neg = leaving
interpretMotion zer = stationary
interpretMotion pos = entering

allNine : List NonaryControlState
allNine =
  control-state neg neg ∷
  control-state neg zer ∷
  control-state neg pos ∷
  control-state zer neg ∷
  control-state zer zer ∷
  control-state zer pos ∷
  control-state pos neg ∷
  control-state pos zer ∷
  control-state pos pos ∷
  []

allNineCount :
  length allNine ≡ 9
allNineCount = refl

canonical-entering-admissible :
  classifyControl 2 0 2 3 ≡ control-state pos pos
canonical-entering-admissible = refl

canonical-stationary-margin :
  classifyControl 2 1 2 2 ≡ control-state zer zer
canonical-stationary-margin = refl

------------------------------------------------------------------------
-- The six-state companion is a ternary carrier with one independent binary
-- context bit.  It is deliberately not identified with the nine-state
-- state/velocity product.

record HexControlState : Set where
  constructor hex-state
  field
    ternaryCarrier : Trit
    contextBit : Bool

open HexControlState public

allSix : List HexControlState
allSix =
  hex-state neg false ∷
  hex-state neg true ∷
  hex-state zer false ∷
  hex-state zer true ∷
  hex-state pos false ∷
  hex-state pos true ∷
  []

allSixCount :
  length allSix ≡ 6
allSixCount = refl
