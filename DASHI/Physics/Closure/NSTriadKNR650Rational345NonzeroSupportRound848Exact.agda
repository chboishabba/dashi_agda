{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345NonzeroSupportRound848Exact where

------------------------------------------------------------------------
-- R848 -> REPAIRED R846 EXACT ORIGINAL SAME-OBJECT ADAPTER.
--
-- The ACTUAL complete six-seed 36-pair support theorem ALREADY EXISTS in:
--   NSTriadKNR650Rational345MixedOutputSupportRound848Exact
--
-- It proves for every NONZERO mode with Snapshot.forcingActive=false
-- that the original filtered physical output fibre is empty.
-- DO NOT duplicate those 36 cases, the R224 zero-pruning proof,
-- R849 global work or R850 instantaneous rate identity.
--
-- R846's old stronger F1 was FALSE at zero (see new R847), where
-- opposite six seed modes give selected cells. Repaired R846 now uses
-- the old R436 transversality zero-output theorem for that case.
--
-- Here is the sole genuinely new transport: convert the executable
-- original modeEqual test against zero into the ORIGINAL
-- Z3.NonZeroMode record, and supply the existing R848 theorem
-- as the exact R846 nonzero-support producer. No Set-oracle.
--
-- This pays the corrected R846 F1 source interface; it does NOT
-- re-prove the already-paid R850 R829 instantaneous rate or inhabit
-- the still-open real-time R408/R830 selected-trajectory transport.
--
-- Source-written only. Pinned local Agda 2.9 receipt required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveRepositoryReductionRound837Exact as R837
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNR650Rational345MixedOutputSupportRound848Exact as Original848
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingSupportMaxCutRound846Exact as R846

booleanNonzeroToActualNonzero :
  (mode : Z3.FourierMode) →
  Output.modeEqual mode Z3.zeroMode ≡ false →
  Z3.NonZeroMode mode
booleanNonzeroToActualNonzero mode falseTest = record
  { Z3.NonZeroMode.notZero = λ same →
      Output.falseNotTrue
        (trans (sym falseTest)
          (Output.modeEqualComplete same))
  }

-- This is the entire repaired finite F1, sourced to the already
-- existing constructive 36-pair theorem.
inactiveNonzeroFibreEmpty : R846.InactiveActiveFibreEmpty
inactiveNonzeroFibreEmpty mode inactive nonzero =
  Original848.mixedFilterEmptyAtInactiveNonzero
    mode (booleanNonzeroToActualNonzero mode nonzero) inactive

-- R846.Evaluate can now consume the explicit inhabited nonzero F1.
-- Its separate zero branch relies on actual R436 transversality.
round846RepairedF1FromOriginalR848 :
  R846.InactiveActiveFibreEmpty
round846RepairedF1FromOriginalR848 = inactiveNonzeroFibreEmpty

-- Construct a real source-specific R837 modal same-object receipt for
-- the literal direct physical snapshot using R844's active forcing
-- rows, original R848 for nonzero support, and R436 for zero output.
-- This is stronger than an isolated certificate of finite-list shape.
F : C3.RealField _
F = Rational.rationalRealField

module ActualDirectPhysicalModal
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  module CompletedR846 =
    R846.Evaluate unit I round846RepairedF1FromOriginalR848

  originalR837ModalSameObject :
    R837.Repository345ModalSameObject (Direct.directPhysicalSystem E I)
  originalR837ModalSameObject = CompletedR846.modalSameObject

-- This does NOT claim all R829D helical 8x2 vector rows via this route;
-- those are separate, and R850 already directly closes the instantaneous
-- physical selected-rate snapshot by its R849/R847 global folds.
