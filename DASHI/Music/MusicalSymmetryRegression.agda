module DASHI.Music.MusicalSymmetryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Music.BooleanMelodySymmetryWitness as Witness
import DASHI.Music.MusicalSymmetryCognitiveBoundary as Boundary

------------------------------------------------------------------------
-- Compact import target for the musical-symmetry tranche.
------------------------------------------------------------------------

repairIdempotenceRegression :
  Witness.copyLeftRepair
    (Witness.copyLeftRepair Witness.m01)
  ≡ Witness.copyLeftRepair Witness.m01
repairIdempotenceRegression = refl

lowBasinRegression :
  Witness.basinVolume Witness.lowAttractor ≡ 2
lowBasinRegression = refl

highBasinRegression :
  Witness.basinVolume Witness.highAttractor ≡ 2
highBasinRegression = refl

structuralGateRegression :
  Boundary.structuralClosed Boundary.canonicalStructuralGate ≡ true
structuralGateRegression = refl

cognitiveNonPromotionRegression :
  Boundary.musicalSymmetryCognitiveExplanationPromoted ≡ false
cognitiveNonPromotionRegression = refl
