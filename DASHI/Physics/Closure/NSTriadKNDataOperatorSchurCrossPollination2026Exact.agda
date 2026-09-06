module DASHI.Physics.Closure.NSTriadKNDataOperatorSchurCrossPollination2026Exact where

------------------------------------------------------------------------
-- 2026 COMPATIBILITY / PROVENANCE SURFACE
--
-- The first PR draft introduced a parallel DataSchur/OperatorSchur owner here.
-- Bidirectional x-pollination has now moved those actual definitions and the
-- proof-bearing OperatorSchur -> DataSchur compiler into the pre-existing
-- authoritative Round-30 Cotlar--Stein owner:
--
--   DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact
--
-- This module remains only as a stable provenance/compatibility surface for
-- the 2026 Lean return. It does not own a second implementation.
--
-- Source calibration:
--   Mischa Cotlar; Elias M. Stein,
--   "A unified theory of Hilbert transforms and ergodic theorems" (1955),
--   DOI not assigned/known.
--
--   RequestProject/NavierStokes/AlmostOrthogonalGramSchur.lean,
--   supplied in the 2026-09-06 Lean handoff archive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact as R30

operatorToDataCompilerClosed : Bool
operatorToDataCompilerClosed = R30.operatorToDataSchurCompilerClosed

physicalOuterCellOperatorSchurSupplied : Bool
physicalOuterCellOperatorSchurSupplied = R30.physicalCrossShellOperatorDecaySupplied

physicalOuterCellDataSchurSupplied : Bool
physicalOuterCellDataSchurSupplied = R30.physicalOuterCellDataSchurSupplied

parallelSchurImplementationRetained : Bool
parallelSchurImplementationRetained = false

operatorToDataCompilerClosedIsTrue : operatorToDataCompilerClosed ≡ true
operatorToDataCompilerClosedIsTrue = R30.operatorToDataSchurCompilerClosedIsTrue

physicalOuterCellOperatorSchurSuppliedIsFalse :
  physicalOuterCellOperatorSchurSupplied ≡ false
physicalOuterCellOperatorSchurSuppliedIsFalse = R30.physicalCrossShellOperatorDecaySuppliedIsFalse

physicalOuterCellDataSchurSuppliedIsFalse :
  physicalOuterCellDataSchurSupplied ≡ false
physicalOuterCellDataSchurSuppliedIsFalse = R30.physicalOuterCellDataSchurSuppliedIsFalse

parallelSchurImplementationRetainedIsFalse :
  parallelSchurImplementationRetained ≡ false
parallelSchurImplementationRetainedIsFalse = refl
