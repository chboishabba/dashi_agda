module DASHI.Physics.Closure.NSTriadKNHHBadScaleInvariantGeometryObstructionRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 36 showed that a genuine bad-stratum dissipative floor
--
--   Gamma_q ~ nu lambda_q
--
-- would manufacture the missing inverse shell scale.  The stabilizer proposal
-- in the continuation analysis suggests defining badness by directional
-- geometry.  This module proves a decisive scaling obstruction to doing that
-- *alone*.
--
-- A direction-only bad witness carries a unit direction, a bad-geometry proof,
-- an amplitude a, and a quadratic dissipative charge W a^2.  Rescaling only
-- the amplitude leaves the direction and the bad-geometry evidence unchanged,
-- while
--
--   D(s a) = s^2 D(a).
--
-- In particular halving amplitude quarters the charge, and setting amplitude
-- to zero preserves the direction-only bad witness while making the quadratic
-- charge exactly zero.  Therefore any uniform dissipative lower floor that is
-- asserted solely from this scale-invariant geometric badness must satisfy
--
--   floor <= 0.
--
-- This is a real no-go result for the proposed HH-bad mechanism: a positive
-- physical floor must carry amplitude/energy normalization, an amplitude-
-- weighted occupation, or another non-scale-invariant hypothesis.  Direction
-- or stabilizer mismatch by itself cannot create an amplitude-independent
-- positive dissipation quantum.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact as Direction

record DirectionOnlyBadWitness
    {geometryLevel : Level}
    (BadGeometry : Direction.UnitDirection → Set geometryLevel) :
    Set (lsuc geometryLevel) where
  constructor direction-only-bad-witness
  field
    direction : Direction.UnitDirection
    badGeometry : BadGeometry direction
    amplitude : ℚ
    dissipationWeight : ℚ

open DirectionOnlyBadWitness public

quadraticDissipation :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel} →
  DirectionOnlyBadWitness BadGeometry → ℚ
quadraticDissipation witness =
  dissipationWeight witness * (amplitude witness * amplitude witness)

scaleAmplitude :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel} →
  ℚ → DirectionOnlyBadWitness BadGeometry →
  DirectionOnlyBadWitness BadGeometry
scaleAmplitude factor witness =
  direction-only-bad-witness
    (direction witness)
    (badGeometry witness)
    (factor * amplitude witness)
    (dissipationWeight witness)

scaledBadDirectionExact :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    factor (witness : DirectionOnlyBadWitness BadGeometry) →
  direction (scaleAmplitude factor witness) ≡ direction witness
scaledBadDirectionExact factor witness = refl

scaledQuadraticDissipationExact :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    factor (witness : DirectionOnlyBadWitness BadGeometry) →
  quadraticDissipation (scaleAmplitude factor witness)
  ≡ (factor * factor) * quadraticDissipation witness
scaledQuadraticDissipationExact factor witness =
  solve
    ( factor
    ∷ amplitude witness
    ∷ dissipationWeight witness
    ∷ [])

half quarter : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4

halveAmplitude :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel} →
  DirectionOnlyBadWitness BadGeometry →
  DirectionOnlyBadWitness BadGeometry
halveAmplitude = scaleAmplitude half

halvingQuartersDissipation :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    (witness : DirectionOnlyBadWitness BadGeometry) →
  quadraticDissipation (halveAmplitude witness)
  ≡ quarter * quadraticDissipation witness
halvingQuartersDissipation witness =
  trans
    (scaledQuadraticDissipationExact half witness)
    (solve (quadraticDissipation witness ∷ []))

quarterPower : Nat → ℚ
quarterPower zero = Int.+ 1 / 1
quarterPower (suc steps) = quarter * quarterPower steps

iterateHalving :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel} →
  Nat → DirectionOnlyBadWitness BadGeometry →
  DirectionOnlyBadWitness BadGeometry
iterateHalving zero witness = witness
iterateHalving (suc steps) witness =
  halveAmplitude (iterateHalving steps witness)

iteratedHalvingPreservesDirection :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    steps (witness : DirectionOnlyBadWitness BadGeometry) →
  direction (iterateHalving steps witness) ≡ direction witness
iteratedHalvingPreservesDirection zero witness = refl
iteratedHalvingPreservesDirection (suc steps) witness =
  iteratedHalvingPreservesDirection steps witness

iteratedHalvingDissipationExact :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    steps (witness : DirectionOnlyBadWitness BadGeometry) →
  quadraticDissipation (iterateHalving steps witness)
  ≡ quarterPower steps * quadraticDissipation witness
iteratedHalvingDissipationExact zero witness =
  solve (quadraticDissipation witness ∷ [])
iteratedHalvingDissipationExact (suc steps) witness =
  trans
    (halvingQuartersDissipation (iterateHalving steps witness))
    (trans
      (cong (quarter *_)
        (iteratedHalvingDissipationExact steps witness))
      (solve
        (quarterPower steps
        ∷ quadraticDissipation witness
        ∷ [])))

zeroAmplitude :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel} →
  DirectionOnlyBadWitness BadGeometry →
  DirectionOnlyBadWitness BadGeometry
zeroAmplitude = scaleAmplitude 0ℚ

zeroAmplitudePreservesDirection :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    (witness : DirectionOnlyBadWitness BadGeometry) →
  direction (zeroAmplitude witness) ≡ direction witness
zeroAmplitudePreservesDirection witness = refl

zeroAmplitudeDissipationZero :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    (witness : DirectionOnlyBadWitness BadGeometry) →
  quadraticDissipation (zeroAmplitude witness) ≡ 0ℚ
zeroAmplitudeDissipationZero witness =
  solve (dissipationWeight witness ∷ amplitude witness ∷ [])

record UniformDirectionOnlyDissipationFloor
    {geometryLevel : Level}
    {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    (floor : ℚ) : Set (lsuc geometryLevel) where
  field
    floorApplies :
      (witness : DirectionOnlyBadWitness BadGeometry) →
      floor ≤ quadraticDissipation witness

open UniformDirectionOnlyDissipationFloor public

uniformDirectionOnlyFloorMustBeNonpositive :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    {floor : ℚ} →
  DirectionOnlyBadWitness BadGeometry →
  UniformDirectionOnlyDissipationFloor {BadGeometry = BadGeometry} floor →
  floor ≤ 0ℚ
uniformDirectionOnlyFloorMustBeNonpositive witness uniformFloor =
  let
    floorAtZero : floor ≤ quadraticDissipation (zeroAmplitude witness)
    floorAtZero = floorApplies uniformFloor (zeroAmplitude witness)
  in
  substUpper floorAtZero (zeroAmplitudeDissipationZero witness)
  where
  substUpper : ∀ {left right final : ℚ} →
    left ≤ right → right ≡ final → left ≤ final
  substUpper inequality refl = inequality

uniformDirectionOnlyFloorSurvivesEveryHalving :
  ∀ {geometryLevel} {BadGeometry : Direction.UnitDirection → Set geometryLevel}
    {floor : ℚ} →
  (witness : DirectionOnlyBadWitness BadGeometry) →
  UniformDirectionOnlyDissipationFloor {BadGeometry = BadGeometry} floor →
  ∀ steps →
  floor ≤ quarterPower steps * quadraticDissipation witness
uniformDirectionOnlyFloorSurvivesEveryHalving witness uniformFloor steps =
  let
    raw = floorApplies uniformFloor (iterateHalving steps witness)
  in
  substUpper raw (iteratedHalvingDissipationExact steps witness)
  where
  substUpper : ∀ {left right final : ℚ} →
    left ≤ right → right ≡ final → left ≤ final
  substUpper inequality refl = inequality

hhBadDirectionOnlyFloorObstructionClosed : Bool
hhBadDirectionOnlyFloorObstructionClosed = true

positiveHHBadFloorRequiresScaleBreakingInput : Bool
positiveHHBadFloorRequiresScaleBreakingInput = true

hhBadDirectionOnlyFloorObstructionClosedIsTrue :
  hhBadDirectionOnlyFloorObstructionClosed ≡ true
hhBadDirectionOnlyFloorObstructionClosedIsTrue = refl

positiveHHBadFloorRequiresScaleBreakingInputIsTrue :
  positiveHHBadFloorRequiresScaleBreakingInput ≡ true
positiveHHBadFloorRequiresScaleBreakingInputIsTrue = refl
