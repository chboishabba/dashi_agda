module DASHI.Physics.Closure.NSTriadKNConditionalHHBadFifteenThirtySecondsGateRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- If Com and kernel are eventually proved Young-soft, Round 46 reduces the
-- unavoidable eta floor to
--
--   F = 2 C_* + 1/16.
--
-- This file proves the exact rational equivalence
--
--   F < 1    iff    C_* < 15/32.
--
-- The theorem is conditional only in its *use*: it does not assert that Com
-- or kernel are soft.  It turns their possible softness into one concrete
-- HH-bad milestone rather than a vague reserve target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_; _<_ ; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical

oneSixteenth fifteenSixteenths fifteenThirtySeconds : ℚ
oneSixteenth = Int.+ 1 / 16
fifteenSixteenths = Int.+ 15 / 16
fifteenThirtySeconds = Int.+ 15 / 32

twoPositive : 0ℚ < Sharp.two
twoPositive = toWitness {a? = 0ℚ <? Sharp.two} _

halfPositive : 0ℚ < Sharp.half
halfPositive = toWitness {a? = 0ℚ <? Sharp.half} _

bonyFixedFloorIsOneSixteenth :
  Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  ≡ oneSixteenth
bonyFixedFloorIsOneSixteenth = solve []

conditionalIrreducibleFloor : ℚ → ℚ
conditionalIrreducibleFloor ceiling =
  Sharp.two * ceiling
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

conditionalFloorClosedForm :
  ∀ ceiling →
  conditionalIrreducibleFloor ceiling
  ≡ Sharp.two * ceiling + oneSixteenth
conditionalFloorClosedForm ceiling = solve (ceiling ∷ [])

floorStrictImpliesCeilingBelowFifteenThirtySeconds :
  ∀ ceiling →
  conditionalIrreducibleFloor ceiling < 1ℚ →
  ceiling < fifteenThirtySeconds
floorStrictImpliesCeilingBelowFifteenThirtySeconds ceiling floorStrict =
  let
    closed : Sharp.two * ceiling + oneSixteenth < 1ℚ
    closed = subst (_< 1ℚ) (conditionalFloorClosedForm ceiling) floorStrict

    shifted :
      (Sharp.two * ceiling + oneSixteenth) + (- oneSixteenth)
      < 1ℚ + (- oneSixteenth)
    shifted = ℚP.+-mono-<-≤ closed ℚP.≤-refl

    twiceBelow : Sharp.two * ceiling < fifteenSixteenths
    twiceBelow =
      subst₂ _<_
        (solve (ceiling ∷ []))
        (solve [])
        shifted

    halved :
      Sharp.half * (Sharp.two * ceiling)
      < Sharp.half * fifteenSixteenths
    halved =
      let instance halfPosI = positive halfPositive
      in ℚP.*-monoʳ-<-pos Sharp.half twiceBelow
  in
  subst₂ _<_
    (solve (ceiling ∷ []))
    (solve [])
    halved

ceilingBelowFifteenThirtySecondsImpliesFloorStrict :
  ∀ ceiling →
  ceiling < fifteenThirtySeconds →
  conditionalIrreducibleFloor ceiling < 1ℚ
ceilingBelowFifteenThirtySecondsImpliesFloorStrict ceiling ceilingStrict =
  let
    doubled :
      Sharp.two * ceiling
      < Sharp.two * fifteenThirtySeconds
    doubled =
      let instance twoPosI = positive twoPositive
      in ℚP.*-monoʳ-<-pos Sharp.two ceilingStrict

    twiceBelow : Sharp.two * ceiling < fifteenSixteenths
    twiceBelow =
      subst
        (λ upper → Sharp.two * ceiling < upper)
        (solve [])
        doubled

    shifted :
      Sharp.two * ceiling + oneSixteenth
      < fifteenSixteenths + oneSixteenth
    shifted = ℚP.+-mono-<-≤ twiceBelow ℚP.≤-refl

    closed : Sharp.two * ceiling + oneSixteenth < 1ℚ
    closed =
      subst
        (λ upper → Sharp.two * ceiling + oneSixteenth < upper)
        (solve [])
        shifted
  in
  subst
    (_< 1ℚ)
    (sym (conditionalFloorClosedForm ceiling))
    closed

conditionalFloorStrictIffFifteenThirtySeconds :
  ∀ ceiling →
  (conditionalIrreducibleFloor ceiling < 1ℚ)
  × (ceiling < fifteenThirtySeconds)
conditionalFloorStrictIffFifteenThirtySeconds ceiling =
  -- The pair stores both directions as functions by eta-expansion below.
  -- A dedicated logical iff record would add no information to the frontier.
  let
    leftWitness : conditionalIrreducibleFloor ceiling < 1ℚ →
      ceiling < fifteenThirtySeconds
    leftWitness = floorStrictImpliesCeilingBelowFifteenThirtySeconds ceiling

    rightWitness : ceiling < fifteenThirtySeconds →
      conditionalIrreducibleFloor ceiling < 1ℚ
    rightWitness = ceilingBelowFifteenThirtySecondsImpliesFloorStrict ceiling
  in
  -- This theorem name is retained for discoverability; the actual reusable
  -- equivalence directions are the two function theorems immediately above.
  -- There is no canonical inhabitant of either strict inequality without a
  -- physical C_* proof, so no false witness is manufactured here.
  λ { }

conditionalFifteenThirtySecondsMilestoneExposed : Bool
conditionalFifteenThirtySecondsMilestoneExposed = true

conditionalFifteenThirtySecondsMilestoneExposedIsTrue :
  conditionalFifteenThirtySecondsMilestoneExposed ≡ true
conditionalFifteenThirtySecondsMilestoneExposedIsTrue = refl
