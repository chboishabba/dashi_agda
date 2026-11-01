module DASHI.Cognition.VisualPatternModeGeometryTests where

------------------------------------------------------------------------
-- Focused structural checks for the visual pattern lane.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringRegime
  ; stationaryFiniteWavelengthTuring
  ; isTuringPatternRegime
  ; ⊤
  ; tt
  )
open import DASHI.Cognition.KlueverFormConstantProjection using
  ( KlueverForm
  ; latticeGrating
  ; spiral
  )
open import DASHI.Cognition.VisualTuringKlueverBridge using
  ( ProjectsAsKluever
  ; stripesAsLattice
  ; spiralAsSpiral
  ; canonicalTuringDerivativeBoundary
  )
open import DASHI.Cognition.ModeSelectionToProjectionLaw using
  ( ManyToOneLatticeWitness
  ; canonicalManyToOneLatticeWitness
  ; NonTotalProjectionWitness
  ; canonicalNonTotalProjectionWitness
  )
open import DASHI.Cognition.VisualPatternModeGeometryBundle using
  ( VisualPatternStructuralClosure
  ; canonicalVisualPatternStructuralClosure
  )

final-regime-check :
  isTuringPatternRegime stationaryFiniteWavelengthTuring
final-regime-check = tt

stripe-lattice-check :
  ProjectsAsKluever DASHI.Biology.TuringPatternRegimeSurface.stripeFamily latticeGrating
stripe-lattice-check = stripesAsLattice

spiral-projection-check :
  ProjectsAsKluever DASHI.Biology.TuringPatternRegimeSurface.spiralFamily spiral
spiral-projection-check = spiralAsSpiral

many-to-one-check : ManyToOneLatticeWitness
many-to-one-check = canonicalManyToOneLatticeWitness

non-total-check : NonTotalProjectionWitness
non-total-check = canonicalNonTotalProjectionWitness

structural-closure-check : VisualPatternStructuralClosure
structural-closure-check = canonicalVisualPatternStructuralClosure
