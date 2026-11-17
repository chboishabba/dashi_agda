module DASHI.Physics.Gravity.KSW668F8SSPRK3RadialLiftNaturalityExact where

------------------------------------------------------------------------
-- XXXVII original F8 stage-composition algebra, NOT SSPRK3 stability.
--
-- Shu-Osher SSPRK3 used in scripts/ksw668_f8_tt_multipole.py:
-- Y1=Y+dt F(T0,Y)
-- Y2=3/4 Y +1/4 [Y1+dt F(T1,Y1)]
-- Y3=1/3 Y +2/3 [Y2+dt F(Tmid,Y2)].
--
-- For a linear semidiscrete operator at each stage with a source,
-- a time-independent rational reconstruction scaling lambda commutes
-- with the three RK stages when the forcing is scaled as well.
-- The coefficients a0,a1,a2 may differ at each stage, reflecting
-- the ACTUAL moving b(T),v(T),amp(T) geometry.
--
-- This is the scalar linear stage law to reuse on the U/P/M
-- augmented-origin diagram. It does not show a single scalar
-- diagonal coefficient represents the original coupled matrix
-- operator, nor does it prove a bound on amplification, uniform
-- CFL, moving-domain source trace or tensor Weyl convergence.
-- Agda pinned kernel NOT RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8AugmentedOriginRadialFVIntertwinerExact as Lift

quarter threeQuarters third twoThirds : ℚ
quarter = (+ 1) / 4
threeQuarters = (+ 3) / 4
third = (+ 1) / 3
twoThirds = (+ 2) / 3

linearStage : ℚ → ℚ → ℚ → ℚ
linearStage a src y = a * y + src

ssprk3First : ℚ → ℚ → ℚ → ℚ → ℚ
ssprk3First dt a src y = y + dt * linearStage a src y

ssprk3Second :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
ssprk3Second dt a0 a1 src0 src1 y =
  let y1 = ssprk3First dt a0 src0 y
  in threeQuarters * y
     + quarter * (y1 + dt * linearStage a1 src1 y1)

ssprk3Third :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
ssprk3Third dt a0 a1 a2 src0 src1 src2 y =
  let y2 = ssprk3Second dt a0 a1 src0 src1 y
  in third * y
     + twoThirds * (y2 + dt * linearStage a2 src2 y2)

firstStageHomogeneous :
  (lambda dt a src y : ℚ) →
  ssprk3First dt a (lambda * src) (lambda * y)
  ≡ lambda * ssprk3First dt a src y
firstStageHomogeneous lambda dt a src y = solve []

secondStageHomogeneous :
  (lambda dt a0 a1 src0 src1 y : ℚ) →
  ssprk3Second dt a0 a1 (lambda * src0) (lambda * src1)
    (lambda * y)
  ≡ lambda * ssprk3Second dt a0 a1 src0 src1 y
secondStageHomogeneous lambda dt a0 a1 src0 src1 y = solve []

thirdStageHomogeneous :
  (lambda dt a0 a1 a2 src0 src1 src2 y : ℚ) →
  ssprk3Third dt a0 a1 a2
    (lambda * src0) (lambda * src1) (lambda * src2)
    (lambda * y)
  ≡ lambda * ssprk3Third dt a0 a1 a2
      src0 src1 src2 y
thirdStageHomogeneous lambda dt a0 a1 a2
  src0 src1 src2 y = solve []
