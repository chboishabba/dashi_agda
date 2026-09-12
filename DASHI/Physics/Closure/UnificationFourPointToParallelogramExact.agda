{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.UnificationFourPointToParallelogramExact where

------------------------------------------------------------------------
-- PAPER 8 / UCT.6 -> UCT.7
--
-- Once the exact four-point cancellation is theorem-bearing on the quotient
-- defect surface, the parallelogram law is not another analytic theorem: it is
-- the same equality under the repository's normalized definition.
--
-- This module makes that compiler explicit.  It does NOT prove the missing
-- UCT.5 -> UCT.6 bridge and does NOT perform Jordan-von Neumann polarization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.DefectFourPointParallelogramLawBoundary as Four

fourPointAxiomsGiveParallelogram :
  ∀ {surface : Four.AbelianQuotientDefectSurface} →
  Four.FourPointDefectAxioms surface →
  Four.ParallelogramLaw surface
fourPointAxiomsGiveParallelogram axioms =
  Four.FourPointDefectAxioms.fourPointDefectZero axioms

asFourPointToQuadraticBoundary :
  ∀ {surface : Four.AbelianQuotientDefectSurface} →
  (axioms : Four.FourPointDefectAxioms surface) →
  Four.FourPointToQuadraticBoundary surface
asFourPointToQuadraticBoundary axioms = record
  { Four.FourPointToQuadraticBoundary.fourPointAxioms = axioms
  ; Four.FourPointToQuadraticBoundary.parallelogramLaw =
      fourPointAxiomsGiveParallelogram axioms
  ; Four.FourPointToQuadraticBoundary.parallelogramLawComesFromFourPointDefect =
      refl
  ; Four.FourPointToQuadraticBoundary.polarizationBoundaryAvailable =
      Agda.Builtin.Bool.true
  ; Four.FourPointToQuadraticBoundary.polarizationBoundaryAvailableIsTrue =
      refl
  ; Four.FourPointToQuadraticBoundary.jordanVonNeumannBoundaryAvailable =
      Agda.Builtin.Bool.true
  ; Four.FourPointToQuadraticBoundary.jordanVonNeumannBoundaryAvailableIsTrue =
      refl
  ; Four.FourPointToQuadraticBoundary.quadraticFormPromoted =
      Agda.Builtin.Bool.false
  ; Four.FourPointToQuadraticBoundary.quadraticFormPromotedIsFalse =
      refl
  }

uct6ToUCT7CompilerLevel : ProofLevel
uct6ToUCT7CompilerLevel = machineChecked

-- The hard theorem is still the upstream construction of broad quotient-level
-- FourPointDefectAxioms, especially the fourPointDefectZero field.
uct6FourPointAxiomsPhysicalLevel : ProofLevel
uct6FourPointAxiomsPhysicalLevel = conditional

uct8JordanVonNeumannPhysicalLevel : ProofLevel
uct8JordanVonNeumannPhysicalLevel = conditional
