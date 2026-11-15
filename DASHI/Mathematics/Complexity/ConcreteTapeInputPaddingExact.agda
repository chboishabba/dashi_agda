module DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact where

------------------------------------------------------------------------
-- LITERAL INPUT ROW -> ANY LARGER FIXED TABLEAU WIDTH
--
-- The minimal initial row already carries explicit boundary blanks.  Here we
-- append arbitrary additional right blanks, prove exact cell count, and retain
-- the initial-state / input-prefix semantics.  This supplies the fixed-width
-- row-0 target consumed by the one-global-vector endpoint CNF.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

replicateBlank :
  ∀ {machine} →
  Nat →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
replicateBlank {machine} zero = []
replicateBlank {machine} (suc n) =
  Local.plain {State = Local.State machine} (Local.blank machine)
  ∷ replicateBlank {machine} n

replicateBlankLength :
  ∀ {machine} (n : Nat) →
  Canonical.listLength (replicateBlank {machine} n) ≡ n
replicateBlankLength zero = refl
replicateBlankLength (suc n) = cong suc (replicateBlankLength n)

replicateBlankPlain :
  ∀ {machine} (n : Nat) →
  WF.PlainCells (replicateBlank {machine} n)
replicateBlankPlain zero =
  WF.plainNil
replicateBlankPlain (suc n) =
  WF.plainCons (replicateBlankPlain n)

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  Canonical.listLength (Local.append xs ys)
  ≡ Canonical.listLength xs + Canonical.listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys = cong suc (appendLength xs ys)

paddedInitialCells :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
paddedInitialCells {machine} input extra =
  Local.append
    (Input.initialInputCells {machine} input)
    (replicateBlank {machine} extra)

paddedInitialRow :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  Local.TapeRow machine
paddedInitialRow {machine} input extra =
  Local.tape-row (paddedInitialCells {machine} input extra)

paddedInitialCellCount :
  ∀ {machine}
    (input : Input.InputWord machine)
    (extra : Nat) →
  Canonical.listLength
    (paddedInitialCells {machine} input extra)
  ≡ Input.initialInputCellCount {machine} input + extra
paddedInitialCellCount {machine} input extra =
  trans
    (appendLength
      (Input.initialInputCells {machine} input)
      (replicateBlank {machine} extra))
    (cong (Input.initialInputCellCount {machine} input +_)
      (replicateBlankLength {machine} extra))

minimalInitialWidth :
  ∀ {machine} →
  Input.InputWord machine →
  Nat
minimalInitialWidth {machine} input =
  Input.initialInputCellCount {machine} input

record WidthExtension
    {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (cols : Nat) : Set where
  constructor width-extension
  field
    extra : Nat
    exact : minimalInitialWidth {machine} input + extra ≡ cols

open WidthExtension public

paddedInitialRowAtWidth :
  ∀ {machine}
    (input : Input.InputWord machine)
    (cols : Nat) →
  WidthExtension {machine} input cols →
  Local.TapeRow machine
paddedInitialRowAtWidth {machine} input cols extension =
  paddedInitialRow {machine} input (extra extension)

paddedInitialRowAtWidth_count :
  ∀ {machine}
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : WidthExtension {machine} input cols) →
  Canonical.listLength
    (Local.cells
      (paddedInitialRowAtWidth {machine} input cols extension))
  ≡ cols
paddedInitialRowAtWidth_count {machine} input cols extension =
  trans
    (paddedInitialCellCount {machine} input (extra extension))
    (exact extension)

paddedInitialBits :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : WidthExtension {machine} input cols) →
  CNF.Bits
    (Canonical.listLength
      (Local.cells
        (paddedInitialRowAtWidth {machine} input cols extension))
      * Canonical.CellWidth machine)
paddedInitialBits {machine} stateCoverage symbolCoverage input cols extension =
  Flat.encodeRow
    stateCoverage symbolCoverage
    (paddedInitialRowAtWidth {machine} input cols extension)

record FixedWidthInputEndpoint
    (machine : Local.ConcreteTapeMachine)
    (input : Input.InputWord machine)
    (cols : Nat) : Set₁ where
  field
    extension : WidthExtension {machine} input cols
    row : Local.TapeRow machine
    rowIsPaddedInput :
      row ≡ paddedInitialRowAtWidth {machine} input cols extension
    rowWidth :
      Canonical.listLength (Local.cells row) ≡ cols

fixedWidthInputEndpoint :
  ∀ (machine : Local.ConcreteTapeMachine)
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : WidthExtension {machine} input cols) →
  FixedWidthInputEndpoint machine input cols
fixedWidthInputEndpoint machine input cols extension = record
  { extension = extension
  ; row = paddedInitialRowAtWidth {machine} input cols extension
  ; rowIsPaddedInput = refl
  ; rowWidth = paddedInitialRowAtWidth_count {machine} input cols extension
  }

record InputPaddingReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    arbitraryRightBlankPaddingPaid : Bool
    exactPaddedWidthPaid : Bool
    fixedWidthEndpointCarrierPaid : Bool
    canonicalFixedWidthBitsPaid : Bool
    choosePolynomialColsPaid : Bool
    headTravelFitsWidthPaid : Bool

inputPaddingReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  InputPaddingReceipt machine
inputPaddingReceipt machine = record
  { arbitraryRightBlankPaddingPaid = true
  ; exactPaddedWidthPaid = true
  ; fixedWidthEndpointCarrierPaid = true
  ; canonicalFixedWidthBitsPaid = true
  ; choosePolynomialColsPaid = false
  ; headTravelFitsWidthPaid = false
  }
