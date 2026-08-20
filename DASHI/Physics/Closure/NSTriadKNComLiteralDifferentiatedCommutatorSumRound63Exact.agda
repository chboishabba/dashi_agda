module DASHI.Physics.Closure.NSTriadKNComLiteralDifferentiatedCommutatorSumRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 B0 SAME-OBJECT WELD
--
-- Round25's physical five-source fibre has four classified TRIADIC sources
-- plus one separately appended `differentiatedCommutator output` cell.  Until
-- now the value of that fifth cell was left to an arbitrary mode-indexed
-- functional.
--
-- Round57/62 meanwhile construct the actual finite complex odd-P/Q collision
-- vector on the same physical output fibre and prove entrywise that it equals
-- the projector commutator (chi_out-chi_in)T.
--
-- This module welds those two lanes without a rational surrogate:
--
--   literalDifferentiatedCommutator(output)
--      := sum (literal oddPQ coefficients on physicalOutputFiber output).
--
-- The Round62 list identity then implies exactly that this fifth-cell value is
-- the sum of the literal projector-commutator coefficients over the SAME
-- incidences.  A complex-valued five-source evaluator is also provided so the
-- appended Round25 cell can be interpreted by this constructed value rather
-- than a free scalar.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQOutputFibreCommutatorRound62Exact as FibreCom
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Five

sumComplex :
  ∀ {r} (F : C3.RealField r) →
  List (C3.Complex F) → C3.Complex F
sumComplex F [] = C3.complexZero F
sumComplex F (value ∷ rest) = C3.complexAdd value (sumComplex F rest)

sumComplexCong :
  ∀ {r} {F : C3.RealField r}
    {left right : List (C3.Complex F)} →
  left ≡ right →
  sumComplex F left ≡ sumComplex F right
sumComplexCong refl = refl

literalDifferentiatedCommutator :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Complex (LP.realField model)
literalDifferentiatedCommutator model projectorCutoff enumerationCutoff E velocity output =
  sumComplex (LP.realField model)
    (Odd.literalOddPQOutputFibreCoefficients
      model projectorCutoff enumerationCutoff E velocity output)

literalProjectorCommutatorSum :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Complex (LP.realField model)
literalProjectorCommutatorSum model projectorCutoff enumerationCutoff E velocity output =
  sumComplex (LP.realField model)
    (FibreCom.literalProjectorCommutatorOutputFibreCoefficients
      model projectorCutoff enumerationCutoff E velocity output)

literalDifferentiatedCommutatorIsProjectorCommutatorSum :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  literalDifferentiatedCommutator
    model projectorCutoff enumerationCutoff E velocity output
  ≡ literalProjectorCommutatorSum
      model projectorCutoff enumerationCutoff E velocity output
literalDifferentiatedCommutatorIsProjectorCommutatorSum
    model projectorCutoff enumerationCutoff E velocity output =
  sumComplexCong
    (FibreCom.literalOddPQOutputFibreIsProjectorCommutatorOutputFibre
      model projectorCutoff enumerationCutoff E velocity output)

literalFiveSourceCellValue :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (triadValue : Physical.PhysicalTriadIncidence → C3.Complex (LP.realField model)) →
  Five.FiveSourceCell → C3.Complex (LP.realField model)
literalFiveSourceCellValue
    model projectorCutoff enumerationCutoff E velocity triadValue
    (Five.triadicSource classified) =
  triadValue (Five.incidence classified)
literalFiveSourceCellValue
    model projectorCutoff enumerationCutoff E velocity triadValue
    (Five.differentiatedCommutator output) =
  literalDifferentiatedCommutator
    model projectorCutoff enumerationCutoff E velocity output

literalAppendedComCellValueExact :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (triadValue : Physical.PhysicalTriadIncidence → C3.Complex (LP.realField model))
    (output : Z3.FourierMode) →
  literalFiveSourceCellValue
    model projectorCutoff enumerationCutoff E velocity triadValue
    (Five.differentiatedCommutator output)
  ≡ literalProjectorCommutatorSum
      model projectorCutoff enumerationCutoff E velocity output
literalAppendedComCellValueExact
    model projectorCutoff enumerationCutoff E velocity triadValue output =
  literalDifferentiatedCommutatorIsProjectorCommutatorSum
    model projectorCutoff enumerationCutoff E velocity output

fifthComCellNowHasLiteralComplexValue : Bool
fifthComCellNowHasLiteralComplexValue = true

fifthComCellIsExactProjectorCommutatorSum : Bool
fifthComCellIsExactProjectorCommutatorSum = true

fifthComCellNowHasLiteralComplexValueIsTrue :
  fifthComCellNowHasLiteralComplexValue ≡ true
fifthComCellNowHasLiteralComplexValueIsTrue = refl

fifthComCellIsExactProjectorCommutatorSumIsTrue :
  fifthComCellIsExactProjectorCommutatorSum ≡ true
fifthComCellIsExactProjectorCommutatorSumIsTrue = refl
