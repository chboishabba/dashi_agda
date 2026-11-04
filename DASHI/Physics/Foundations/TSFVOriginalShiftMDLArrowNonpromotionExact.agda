module DASHI.Physics.Foundations.TSFVOriginalShiftMDLArrowNonpromotionExact where

------------------------------------------------------------------------
-- P01.L08/L10 and P02.L14: exact SOURCE-ARCHAEOLOGY boundary between
-- the original shift/MDL construction and the original observer arrow.
--
-- Important OWNED facts, not new arbitrary axioms:
-- (i) ShiftLorentzEmergenceInstance.ShiftArrow x = 0 for EVERY selected
--     ternary shift state, by its ORIGINAL source definition;
-- (ii) ShiftRGObservableInstance.shiftCoarseFixed proves an actual
--     original shift-fixed coarse state;
-- (iii) FiniteHistoryOrientationExact contains two distinct selected
--     hidden histories that give the same earlier record.
--
-- Hence the original constant ShiftArrow output CANNOT recover which
-- original history is selected under ANY putative history->shift map.
-- And no globally strictly decreasing Nat-valued MDL of the current
-- original shift step exists, because it has a fixed state.
--
-- The earlier shift cone/quadratic/MDL nonincrease proofs are genuine
-- reusable source results. This does NOT refute emergence from a
-- DIFFERENT physically measured time observable on the same carrier,
-- a selected boundary, or an observer quotient after coarse graining.
-- Construction of that actual map remains the physical next lemma.
--
-- Imported shift modules do not form a verified transitive --safe root;
-- no Golden annotation or kernel acceptance claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_<_)
open import Data.Nat.Properties as NatP using (<-irrefl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.RealTernaryCarrier as RTC
import DASHI.Geometry.ShiftLorentzEmergenceInstance as Shift
import DASHI.Physics.Closure.ShiftRGObservableInstance as ShiftRG
import DASHI.Physics.Foundations.FiniteHistoryOrientationExact as Micro

ShiftState13 : Set
ShiftState13 = RTC.Carrier (suc zero + suc (suc (suc zero)))

originalShiftArrow13 : ShiftState13 → Nat
originalShiftArrow13 =
  Shift.ShiftArrow {m = suc zero} {k = suc (suc (suc zero))}

-- The literal current shift-arrow declaration is constant zero, not
-- an independently measured observer time-orientation functional.
originalSelectedShiftArrowIsConstant :
  ∀ state → originalShiftArrow13 state ≡ zero
originalSelectedShiftArrowIsConstant state = refl

-- The original two hidden histories cannot be distinguished from a
-- value that is identically 0, however the selected history is encoded
-- into shift states. This rejects a false physical arrow source.
noOriginalHistoryDecoderFromShiftArrow :
  (encode : Micro.History2 → ShiftState13)
  (decode : Nat → Micro.History2) →
  ((choice : Micro.LaterChoice) →
    decode (originalShiftArrow13 (encode (Micro.hiddenHistory choice)))
    ≡ Micro.hiddenHistory choice) →
  ⊥
noOriginalHistoryDecoderFromShiftArrow encode decode correct =
  Micro.futureBoundaryCanChangeHiddenHistory
    (trans
      (sym (correct Micro.chooseMinusBoundary))
      (trans
        (cong decode
          (trans
            (originalSelectedShiftArrowIsConstant
              (encode (Micro.hiddenHistory Micro.chooseMinusBoundary)))
            (sym (originalSelectedShiftArrowIsConstant
              (encode (Micro.hiddenHistory Micro.choosePlusBoundary))))))
        (correct Micro.choosePlusBoundary)))

-- A stronger obstruction to promoting weak MDL nonincrease into
-- UNIVERSAL STRICT decrease for the same selected shift step.
-- Original shiftCoarseFixed provides the actual witness of a fixed state.
originalShiftHasCoarseFixedPoint :
  Shift.ShiftStep
    (ShiftRG.shiftCoarse Shift.canonicalShiftStateWitness)
  ≡ ShiftRG.shiftCoarse Shift.canonicalShiftStateWitness
originalShiftHasCoarseFixedPoint =
  ShiftRG.shiftCoarseFixed Shift.canonicalShiftStateWitness

originalShiftMDLCannotAlwaysStrictlyDecrease :
  ((x : ShiftState13) →
    Shift.ShiftMDL (Shift.ShiftStep x) < Shift.ShiftMDL x) →
  ⊥
originalShiftMDLCannotAlwaysStrictlyDecrease strict =
  NatP.<-irrefl
    (cong Shift.ShiftMDL originalShiftHasCoarseFixedPoint)
    (strict (ShiftRG.shiftCoarse Shift.canonicalShiftStateWitness))

-- This is NO claim that the original MDL nonincrease is false:
-- it establishes precisely why <= cannot be silently upgraded to <
-- for EVERY state in the original selected shift carrier.
