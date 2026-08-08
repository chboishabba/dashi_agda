module DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Every coordinate of the finite Galerkin right-hand side is represented by
-- an explicit list of linear viscous atoms and bilinear resonant-triad atoms.
-- The syntax has degree at most two by construction.  Evaluation over Q is
-- literal, and the exact difference identity
--
--   xy-uv = (x-u)y + u(y-v)
--
-- is proved cellwise and for finite sums.  This is the algebraic input to the
-- usual finite-dimensional local-Lipschitz theorem; the continuum-real normed
-- Picard-Lindelof instance remains a separate analytic producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical

data CoordinateAxis : Set where
  xAxis yAxis zAxis : CoordinateAxis

data CoordinatePart : Set where
  realPart imaginaryPart : CoordinatePart

record CoordinateVariable : Set where
  constructor coordinate-variable
  field
    variableMode : Z3.FourierMode
    variableAxis : CoordinateAxis
    variablePart : CoordinatePart

open CoordinateVariable public

data GalerkinCoordinateAtom : Set where
  viscousLinear :
    (output : Z3.FourierMode) →
    (component : CoordinateVariable) →
    (coefficient : ℚ) →
    GalerkinCoordinateAtom

  resonantBilinear :
    (triad : Physical.PhysicalTriadIncidence) →
    (left right : CoordinateVariable) →
    (coefficient : ℚ) →
    GalerkinCoordinateAtom

atomDegree : GalerkinCoordinateAtom → Nat
atomDegree (viscousLinear output component coefficient) = suc zero
atomDegree (resonantBilinear triad left right coefficient) = suc (suc zero)

atomDegreeAtMostTwo :
  (atom : GalerkinCoordinateAtom) →
  atomDegree atom ≤ suc (suc zero)
atomDegreeAtMostTwo (viscousLinear output component coefficient) =
  s≤s z≤n
atomDegreeAtMostTwo (resonantBilinear triad left right coefficient) =
  s≤s (s≤s z≤n)

Assignment : Set
Assignment = CoordinateVariable → ℚ

evaluateAtom : GalerkinCoordinateAtom → Assignment → ℚ
evaluateAtom (viscousLinear output component coefficient) state =
  coefficient * state component
evaluateAtom (resonantBilinear triad left right coefficient) state =
  coefficient * state left * state right

evaluateAtoms : List GalerkinCoordinateAtom → Assignment → ℚ
evaluateAtoms [] state = 0ℚ
evaluateAtoms (atom ∷ rest) state =
  evaluateAtom atom state + evaluateAtoms rest state

differenceAtom :
  GalerkinCoordinateAtom → Assignment → Assignment → ℚ
differenceAtom (viscousLinear output component coefficient) state reference =
  coefficient * (state component - reference component)
differenceAtom (resonantBilinear triad left right coefficient) state reference =
  coefficient
  * ((state left - reference left) * state right
    + reference left * (state right - reference right))

atomDifferenceFactorisation :
  (atom : GalerkinCoordinateAtom) →
  (state reference : Assignment) →
  evaluateAtom atom state - evaluateAtom atom reference
  ≡ differenceAtom atom state reference
atomDifferenceFactorisation
  (viscousLinear output component coefficient) state reference =
  solve (coefficient ∷ state component ∷ reference component ∷ [])
atomDifferenceFactorisation
  (resonantBilinear triad left right coefficient) state reference =
  solve
    ( coefficient
    ∷ state left ∷ reference left
    ∷ state right ∷ reference right
    ∷ [])

differenceAtoms :
  List GalerkinCoordinateAtom → Assignment → Assignment → ℚ
differenceAtoms [] state reference = 0ℚ
differenceAtoms (atom ∷ rest) state reference =
  differenceAtom atom state reference
  + differenceAtoms rest state reference

finiteGalerkinDifferenceFactorisation :
  (atoms : List GalerkinCoordinateAtom) →
  (state reference : Assignment) →
  evaluateAtoms atoms state - evaluateAtoms atoms reference
  ≡ differenceAtoms atoms state reference
finiteGalerkinDifferenceFactorisation [] state reference = solve []
finiteGalerkinDifferenceFactorisation (atom ∷ rest) state reference =
  trans
    (solve
      ( evaluateAtom atom state
      ∷ evaluateAtom atom reference
      ∷ evaluateAtoms rest state
      ∷ evaluateAtoms rest reference
      ∷ []))
    (cong₂ _+_
      (atomDifferenceFactorisation atom state reference)
      (finiteGalerkinDifferenceFactorisation rest state reference))

record LiteralGalerkinCoordinateEquation : Set where
  constructor literal-galerkin-coordinate-equation
  field
    outputMode : Z3.FourierMode
    outputVariable : CoordinateVariable
    rightHandSideAtoms : List GalerkinCoordinateAtom

open LiteralGalerkinCoordinateEquation public

coordinateRightHandSide :
  LiteralGalerkinCoordinateEquation → Assignment → ℚ
coordinateRightHandSide equation =
  evaluateAtoms (rightHandSideAtoms equation)

coordinateRightHandSideDifference :
  (equation : LiteralGalerkinCoordinateEquation) →
  (state reference : Assignment) →
  coordinateRightHandSide equation state
    - coordinateRightHandSide equation reference
  ≡ differenceAtoms (rightHandSideAtoms equation) state reference
coordinateRightHandSideDifference equation =
  finiteGalerkinDifferenceFactorisation (rightHandSideAtoms equation)
