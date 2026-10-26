module DASHI.Unified.HornStageClearanceC3SourceCutExact where

-- Source roots: Hatcher, Algebraic Topology Example 2B.2
-- (nested compact stages X_n, B = intersection X_n and marked
-- commutator meridians). The separate three-satellite embedding,
-- actual C3 action and van Kampen collar machinery belong to
-- existing Agda PR #1244, not this source-conditional module.
--
-- This module discharges the GENERAL SET-THEORETIC part of the
-- stage-clearance acceptance: a loop avoiding X_n automatically
-- avoids the limit B and each later X_m. A real short Hatcher
-- meridian with correct free-group marking and finite-stage
-- avoidance remains a SOURCE INPUT, not a constructed witness.
--
-- Agda kernel/typecheck is NOT claimed.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Empty using (⊥)

record Coord3 (A : Set) : Set where
  constructor coord3
  field
    x y z : A

rotateC3 : {A : Set} → Coord3 A → Coord3 A
rotateC3 (coord3 x y z) = coord3 z x y

rotateC3Cubed : {A : Set} → (p : Coord3 A) →
  rotateC3 (rotateC3 (rotateC3 p)) ≡ p
rotateC3Cubed (coord3 x y z) = refl

record NestedHornStages (Point : Set) : Set₁ where
  field
    stage : Nat → Point → Set
    limitBall : Point → Set

    -- For n <= m, X_m is included in X_n.
    laterStageInside : (n m : Nat) → n ≤ m →
      (p : Point) → stage m p → stage n p

    -- The wild ball is contained in EVERY finite X_n.
    limitInsideStage : (n : Nat) → (p : Point) →
      limitBall p → stage n p

open NestedHornStages public

-- LoopImage is a point predicate. Nothing about its geometrical
-- length or its actual free-group generator is presumed.
avoidsLimitFromFiniteStage :
  {Point : Set} →
  (S : NestedHornStages Point) →
  (n : Nat) →
  (loopImage : Point → Set) →
  ((p : Point) → loopImage p → stage S n p → ⊥) →
  (p : Point) → loopImage p → limitBall S p → ⊥
avoidsLimitFromFiniteStage S n loopImage finiteAvoid p hp hb =
  finiteAvoid p hp (limitInsideStage S n p hb)

avoidsAllLaterStages :
  {Point : Set} →
  (S : NestedHornStages Point) →
  (n m : Nat) → n ≤ m →
  (loopImage : Point → Set) →
  ((p : Point) → loopImage p → stage S n p → ⊥) →
  (p : Point) → loopImage p → stage S m p → ⊥
avoidsAllLaterStages S n m hnm loopImage finiteAvoid p hp hm =
  finiteAvoid p hp (laterStageInside S n m hnm p hm)

-- Explicit uninhabited SOURCE-OBLIGATION interface. Constructing
-- a true Hatcher source local meridian would additionally have
-- to provide (1) the ambient Euclidean embedding, (2) source
-- generator/van Kampen marking, (3) length and distance to X_n.
-- These are deliberately NOT conjured from the three-cycle.
record MarkedSourceMeridian (Point : Set)
  (S : NestedHornStages Point) : Set₁ where
  field
    depth : Nat
    image : Point → Set
    avoidsStage : (p : Point) → image p → stage S depth p → ⊥
    sourceMarkingClaim : Set
    sourceMarkingWitness : sourceMarkingClaim

open MarkedSourceMeridian public

markedMeridianAvoidsLimit :
  {Point : Set} →
  (S : NestedHornStages Point) →
  (M : MarkedSourceMeridian Point S) →
  (p : Point) → image M p → limitBall S p → ⊥
markedMeridianAvoidsLimit S M =
  avoidsLimitFromFiniteStage S (depth M) (image M) (avoidsStage M)
