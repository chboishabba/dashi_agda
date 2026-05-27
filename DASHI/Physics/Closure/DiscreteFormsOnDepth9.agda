module DASHI.Physics.Closure.DiscreteFormsOnDepth9 where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

open import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt using
  (DiscreteForms; canonicalDiscreteForms)

open DiscreteForms public

------------------------------------------------------------------------
-- Depth-9 consumer for the Gate 3 discrete geometry witness.
--
-- This module is intentionally thin: it consumes the existing discrete-form
-- witness bundle and records the exact `dSquaredZeroTarget` surface already
-- present in the Gate 3 receipt.  No postulates or placeholder constructors
-- are introduced.

record DiscreteFormsOnDepth9 : Set₁ where
  field
    discreteForms :
      DiscreteForms

    discreteFormsIsCanonical :
      discreteForms ≡ canonicalDiscreteForms

    dSquaredZeroTarget :
      Set

    dSquaredZeroTargetIsCanonical :
      dSquaredZeroTarget
      ≡
      DiscreteForms.dSquaredZeroTarget canonicalDiscreteForms

    selectedExteriorDerivativeSquaredZeroWitness :
      YMObs.YMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroWitnessIsCanonical :
      selectedExteriorDerivativeSquaredZeroWitness
      ≡
      YMObs.canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness

    selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluation :
      (f : SFGC.SFGCSite2DDiscrete0Form) →
      (base : SFGC.SFGCSite2D) →
      SFGC.sfgcSite2DEvaluate2
        (SFGC.sfgcSite2Dδ₁ (SFGC.sfgcSite2Dδ₀ f))
        (SFGC.sfgcSite2DPlaquetteAt base)
      ≡
      SFGC.sfgcSite2DEvaluate2
        SFGC.sfgcSite2DZero2Form
        (SFGC.sfgcSite2DPlaquetteAt base)

    selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluationIsCanonical :
      selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluation
      ≡
      YMObs.sfgcFlatPlaquetteStokesSupportFromSelectedExteriorWitness

    depth9Boundary :
      List String

canonicalDiscreteFormsOnDepth9 : DiscreteFormsOnDepth9
canonicalDiscreteFormsOnDepth9 =
  record
    { discreteForms =
        canonicalDiscreteForms
    ; discreteFormsIsCanonical =
        refl
    ; dSquaredZeroTarget =
        DiscreteForms.dSquaredZeroTarget canonicalDiscreteForms
    ; dSquaredZeroTargetIsCanonical =
        refl
    ; selectedExteriorDerivativeSquaredZeroWitness =
        YMObs.canonicalYMSFGCSelectedExteriorDerivativeSquaredZeroWitness
    ; selectedExteriorDerivativeSquaredZeroWitnessIsCanonical =
        refl
    ; selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluation =
        YMObs.sfgcFlatPlaquetteStokesSupportFromSelectedExteriorWitness
    ; selectedExteriorDerivativeSquaredZeroOnPlaquetteEvaluationIsCanonical =
        refl
    ; depth9Boundary =
        "Depth-9 consumer reuses the canonical Gate 3 discrete forms witness"
        ∷ "The exact dSquaredZeroTarget surface is carried through unchanged"
        ∷ "The concrete selected exterior d^2 = 0 plaquette-evaluation witness is carried through from SFGC.sfgcSite2DP2P3BoundaryOfBoundaryZero"
        ∷ "No new proof obligations, postulates, or placeholder constructors are introduced"
        ∷ []
    }
