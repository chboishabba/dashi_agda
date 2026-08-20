module DASHI.Physics.Closure.NSTriadKNC4cWeightedTransportCommutatorRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND87 / C4c COMMUTATOR NORMAL FORM
--
-- A divergence-free transport is skew-adjoint, but C4c differentiates packet-
-- and derivative-weighted quadratic observables rather than total kinetic
-- energy.  Therefore the surviving advective term is a commutator with the
-- observation/weight, not the homogeneous transport energy.
--
-- This file proves the complete algebra on an arbitrary rational two-channel
-- skew transport and arbitrary symmetric observation matrix.  Write
--
--      T = [ 0  -a ]       W = [ b  c ]
--          [ a   0 ]           [ c  d ].
--
-- For u=(x,y), exact polynomial algebra gives
--
--   <Tu,Wu> + <u,W Tu> = <u,(W T - T W)u>.
--
-- When W=I the commutator is zero and ordinary energy cancellation is
-- recovered.  For nontrivial packet/derivative weights the commutator need not
-- vanish.  Round40 already proves the literal finite-Fourier transport
-- coefficient is skew-adjoint entrywise; Round62 identifies the literal odd
-- P/Q row with a projector commutator.  What remains for C4c is the SAME-OBJECT
-- weld from the Round84 compact-transfer advective derivative to the relevant
-- finite packet/weight commutators and their existing shell bounds.
--
-- The two-channel theorem is a normal-form calculation, not a claim that the
-- full Fourier carrier has only two modes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record Vec2 : Set where
  constructor v2
  field x y : ℚ
open Vec2 public

record SymmetricWeight2 : Set where
  constructor symmetric-weight2
  field w11 w12 w22 : ℚ
open SymmetricWeight2 public

dot : Vec2 → Vec2 → ℚ
dot (v2 x1 y1) (v2 x2 y2) = x1 * x2 + y1 * y2

skewTransport : ℚ → Vec2 → Vec2
skewTransport a (v2 vx vy) = v2 (0ℚ - a * vy) (a * vx)

applyWeight : SymmetricWeight2 → Vec2 → Vec2
applyWeight W (v2 vx vy) =
  v2 (w11 W * vx + w12 W * vy)
     (w12 W * vx + w22 W * vy)

subtractVec : Vec2 → Vec2 → Vec2
subtractVec (v2 ax ay) (v2 bx by) = v2 (ax - bx) (ay - by)

weightTransportCommutator : ℚ → SymmetricWeight2 → Vec2 → Vec2
weightTransportCommutator a W u =
  subtractVec
    (applyWeight W (skewTransport a u))
    (skewTransport a (applyWeight W u))

weightedAdvectiveQuadraticDrift : ℚ → SymmetricWeight2 → Vec2 → ℚ
weightedAdvectiveQuadraticDrift a W u =
  dot (skewTransport a u) (applyWeight W u)
  + dot u (applyWeight W (skewTransport a u))

commutatorQuadraticForm : ℚ → SymmetricWeight2 → Vec2 → ℚ
commutatorQuadraticForm a W u =
  dot u (weightTransportCommutator a W u)

weightedDriftEqualsCommutatorQuadraticForm : ∀ a W u →
  weightedAdvectiveQuadraticDrift a W u
  ≡ commutatorQuadraticForm a W u
weightedDriftEqualsCommutatorQuadraticForm a
    (symmetric-weight2 b c d) (v2 vx vy) =
  solve (a ∷ b ∷ c ∷ d ∷ vx ∷ vy ∷ [])

identityWeight : SymmetricWeight2
identityWeight = symmetric-weight2 1ℚ 0ℚ 1ℚ

identityWeightCommutatorZero : ∀ a u →
  commutatorQuadraticForm a identityWeight u ≡ 0ℚ
identityWeightCommutatorZero a (v2 vx vy) =
  solve (a ∷ vx ∷ vy ∷ [])

identityWeightAdvectiveDriftZero : ∀ a u →
  weightedAdvectiveQuadraticDrift a identityWeight u ≡ 0ℚ
identityWeightAdvectiveDriftZero a u
  rewrite weightedDriftEqualsCommutatorQuadraticForm a identityWeight u
        | identityWeightCommutatorZero a u = refl

-- Exact witness that skewness alone does not kill a weighted observable.
anisotropicWeight : SymmetricWeight2
anisotropicWeight = symmetric-weight2 1ℚ 0ℚ 0ℚ

witnessState : Vec2
witnessState = v2 1ℚ 1ℚ

weightedDriftCanBeNonzero :
  weightedAdvectiveQuadraticDrift 1ℚ anisotropicWeight witnessState
  ≡ - 2ℚ
weightedDriftCanBeNonzero = refl

round87TwoChannelWeightedAdvectiveDriftIsCommutatorExact : Bool
round87TwoChannelWeightedAdvectiveDriftIsCommutatorExact = true

round87GlobalTransportSkewAloneMakesWeightedDriftZero : Bool
round87GlobalTransportSkewAloneMakesWeightedDriftZero = false

round87LiteralRound84AdvectiveShareToPacketCommutatorWeldConstructed : Bool
round87LiteralRound84AdvectiveShareToPacketCommutatorWeldConstructed = false

round87TwoChannelWeightedAdvectiveDriftIsCommutatorExactIsTrue :
  round87TwoChannelWeightedAdvectiveDriftIsCommutatorExact ≡ true
round87TwoChannelWeightedAdvectiveDriftIsCommutatorExactIsTrue = refl

round87GlobalTransportSkewAloneMakesWeightedDriftZeroIsFalse :
  round87GlobalTransportSkewAloneMakesWeightedDriftZero ≡ false
round87GlobalTransportSkewAloneMakesWeightedDriftZeroIsFalse = refl

round87LiteralRound84AdvectiveShareToPacketCommutatorWeldConstructedIsFalse :
  round87LiteralRound84AdvectiveShareToPacketCommutatorWeldConstructed ≡ false
round87LiteralRound84AdvectiveShareToPacketCommutatorWeldConstructedIsFalse = refl
