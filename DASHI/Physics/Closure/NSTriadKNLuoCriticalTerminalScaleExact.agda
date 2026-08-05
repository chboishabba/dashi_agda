module DASHI.Physics.Closure.NSTriadKNLuoCriticalTerminalScaleExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Repository-original correction of the terminal-window scale interface;
-- no DOI is assigned.
--
-- Related harmonic-analysis reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Formalise the corrected critical terminal quantity
--
--   A_q^2 = lambda_q D_q.
--
-- A root r_D with D_q=r_D^2 and a half-frequency h_q with
-- lambda_q=h_q^2 produce
--
--   A_q = h_q r_D,
--   A_q^2 = lambda_q D_q.
--
-- This is the missing half-frequency left by the round-ten energy/Bernstein
-- audit.  The closure theorem below composes a genuine classwise interaction
-- estimate C A_q E_q with the existing 1/64 budget.  It does not assert that
-- energy alone makes A_q small.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record CriticalTailGeometry : Set where
  constructor critical-tail-geometry
  field
    outputHalfScale outputScale : ℚ
    tailRoot tailMass : ℚ
    outputScaleIsSquare :
      outputScale ≡ outputHalfScale * outputHalfScale
    tailMassIsSquare :
      tailMass ≡ tailRoot * tailRoot

open CriticalTailGeometry public

criticalTailRoot : CriticalTailGeometry → ℚ
criticalTailRoot geometry =
  outputHalfScale geometry * tailRoot geometry

criticalTailSquare : CriticalTailGeometry → ℚ
criticalTailSquare geometry =
  criticalTailRoot geometry * criticalTailRoot geometry

criticalTailSquareIdentity :
  (geometry : CriticalTailGeometry) →
  criticalTailSquare geometry
  ≡ outputScale geometry * tailMass geometry
criticalTailSquareIdentity geometry
  rewrite outputScaleIsSquare geometry
        | tailMassIsSquare geometry =
  solve
    ( outputHalfScale geometry
    ∷ tailRoot geometry
    ∷ [])

oneSixtyFourth : ℚ
oneSixtyFourth = Int.+ 1 / 64

record CriticalTerminalClosureData : Set where
  constructor critical-terminal-closure-data
  field
    geometry : CriticalTailGeometry
    interaction coefficient shellEnergy : ℚ
    shellEnergyNonnegative : 0ℚ ≤ shellEnergy
    interactionBound :
      interaction
      ≤ coefficient * criticalTailRoot geometry * shellEnergy
    coefficientCriticalRootSmallness :
      coefficient * criticalTailRoot geometry ≤ oneSixtyFourth

open CriticalTerminalClosureData public

criticalTerminalClosure :
  (closureData : CriticalTerminalClosureData) →
  interaction closureData
  ≤ oneSixtyFourth * shellEnergy closureData
criticalTerminalClosure closureData =
  let
    scaled :
      (coefficient closureData
        * criticalTailRoot (geometry closureData))
        * shellEnergy closureData
      ≤ oneSixtyFourth * shellEnergy closureData
    scaled =
      let
        instance
          energyIsNonnegative =
            nonNegative (shellEnergyNonnegative closureData)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (shellEnergy closureData)
        (coefficientCriticalRootSmallness closureData)
  in
  ℚₚ.≤-trans (interactionBound closureData) scaled
