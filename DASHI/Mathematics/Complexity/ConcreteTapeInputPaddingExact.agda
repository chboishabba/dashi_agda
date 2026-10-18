module DASHI.Mathematics.Complexity.ConcreteTapeInputPaddingExact where

------------------------------------------------------------------------
-- LITERAL INPUT ROW -> ANY LARGER FIXED TABLEAU WIDTH
--
-- The minimal initial row already carries explicit boundary blanks.  Here we
-- append arbitrary additional right blanks, prove exact cell count, and retain
-- the initial-state / input-prefix semantics.  This supplies the fixed-width
-- row-0 target consumed by the one-global-vector endpoint CNF.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

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
  Local.plain (Local.blank machine)
  ∷ replicateBlank n

replicateBlankLength :
  ∀ {machine} (n : Nat) →
  Canonical.listLength (replicateBlank {machine} n) ≡ n
replicateBlankLength zero = refl
replicateBlankLength (suc n)
    rewrite replicateBlankLength n =
  refl

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
appendLength (x ∷ xs) ys
    rewrite appendLength xs ys =
  refl

paddedInitialCells :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
paddedInitialCells input extra =
  Local.append
    (Input.initialInputCells input)
    (replicateBlank extra)

paddedInitialRow :
  ∀ {machine} →
  Input.InputWord machine →
  Nat →
  Local.TapeRow machine
paddedInitialRow input extra =
  Local.tape-row (paddedInitialCells input extra)

paddedInitialCellCount :
  ∀ {machine}
    (input : Input.InputWord machine)
    (extra : Nat) →
  Canonical.listLength
    (paddedInitialCells input extra)
  ≡ Input.initialInputCellCount input + extra
paddedInitialCellCount input extra
    rewrite appendLength
      (Input.initialInputCells input)
      (replicateBlank extra)
          | replicateBlankLength extra =
  refl

minimalInitialWidth :
  ∀ {machine} →
  Input.InputWord machine →
  Nat
minimalInitialWidth input =
  Input.initialInputCellCount input

record WidthExtension
    {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (cols : Nat) : Set where
  constructor width-extension
  field
    extra : Nat
    exact : minimalInitialWidth input + extra ≡ cols

open WidthExtension public

paddedInitialRowAtWidth :
  ∀ {machine}
    (input : Input.InputWord machine)
    (cols : Nat) →
  WidthExtension input cols →
  Local.TapeRow machine
paddedInitialRowAtWidth input cols extension =
  paddedInitialRow input (extra extension)

paddedInitialRowAtWidth_count :
  ∀ {machine}
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : WidthExtension input cols) →
  Canonical.listLength
    (Local.cells
      (paddedInitialRowAtWidth input cols extension))
  ≡ cols
paddedInitialRowAtWidth_count input cols extension
    rewrite paddedInitialCellCount input (extra extension)
          | exact extension =
  refl

paddedInitialBits :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : WidthExtension input cols) →
  CNF.Bits
    (Canonical.listLength
      (Local.cells
        (paddedInitialRowAtWidth input cols extension))
      * Canonical.CellWidth machine)
paddedInitialBits stateCoverage symbolCoverage input cols extension =
  Flat.encodeRow
    stateCoverage symbolCoverage
    (paddedInitialRowAtWidth input cols extension)

record FixedWidthInputEndpoint
    (machine : Local.ConcreteTapeMachine)
    (input : Input.InputWord machine)
    (cols : Nat) : Set₁ where
  field
    extension : WidthExtension input cols
    row : Local.TapeRow machine
    rowIsPaddedInput :
      row ≡ paddedInitialRowAtWidth input cols extension
    rowWidth :
      Canonical.listLength (Local.cells row) ≡ cols

fixedWidthInputEndpoint :
  ∀ (machine : Local.ConcreteTapeMachine)
    (input : Input.InputWord machine)
    (cols : Nat)
    (extension : WidthExtension input cols) →
  FixedWidthInputEndpoint machine input cols
fixedWidthInputEndpoint machine input cols extension = record
  { extension = extension
  ; row = paddedInitialRowAtWidth input cols extension
  ; rowIsPaddedInput = refl
  ; rowWidth = paddedInitialRowAtWidth_count input cols extension
  }

record InputPaddingReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    arbitraryRightBlankPaddingPaid : Agda.Builtin.Bool.Bool
    exactPaddedWidthPaid : Agda.Builtin.Bool.Bool
    fixedWidthEndpointCarrierPaid : Agda.Builtin.Bool.Bool
    canonicalFixedWidthBitsPaid : Agda.Builtin.Bool.Bool
    choosePolynomialColsPaid : Agda.Builtin.Bool.Bool
    headTravelFitsWidthPaid : Agda.Builtin.Bool.Bool

inputPaddingReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  InputPaddingReceipt machine
inputPaddingReceipt machine = record
  { arbitraryRightBlankPaddingPaid = Agda.Builtin.Bool.true
  ; exactPaddedWidthPaid = Agda.Builtin.Bool.true
  ; fixedWidthEndpointCarrierPaid = Agda.Builtin.Bool.true
  ; canonicalFixedWidthBitsPaid = Agda.Builtin.Bool.true
  ; choosePolynomialColsPaid = Agda.Builtin.Bool.false
  ; headTravelFitsWidthPaid = Agda.Builtin.Bool.false
  }
