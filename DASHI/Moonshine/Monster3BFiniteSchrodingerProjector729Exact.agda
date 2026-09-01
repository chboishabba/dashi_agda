module DASHI.Moonshine.Monster3BFiniteSchrodingerProjector729Exact where

------------------------------------------------------------------------
-- SIX CHARACTER PROJECTORS PRODUCE THE EXACT 3^6 = 729 SCALAR
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Moonshine.Monster3BFiniteSchrodingerPointProjectorEvaluationExact as Eval

sixTriplesAre729 : (a : C3.Cyclotomic3) →
  Eval.triple6 a ≡ L.scale 729 a
sixTriplesAre729 (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ [])) (solve (b ∷ []))

record Projector729Boundary : Set where
  constructor projector729Boundary
  field
    sixCoordinateProjectorScaleIs729 : Bool
open Projector729Boundary public

canonicalProjector729Boundary : Projector729Boundary
canonicalProjector729Boundary = projector729Boundary true
