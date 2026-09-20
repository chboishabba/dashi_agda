module DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact where

------------------------------------------------------------------------
-- INPUT WORD -> LITERAL PADDED INITIAL TAPE ROW
--
-- A Cook--Levin reduction is parameterized by the input instance, not merely
-- by the machine.  The existing InitialInteriorRow only required the head
-- state to be the initial state.  This module supplies the missing same-object
-- constructor tying the first tableau row to an actual input word.
--
-- Convention:
--
--   []        ↦  blank | [q₀,blank] | blank
--   a ∷ rest  ↦  blank | [q₀,a]     | rest-as-plain ++ blank
--
-- The explicit blanks make the head interior, matching the locality theorem's
-- padded-tableau convention.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeLocalityCharacterizationExact as Locality
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical

InputWord :
  Local.ConcreteTapeMachine → Set
InputWord machine =
  List (Local.Symbol machine)

plainSymbols :
  ∀ {machine} →
  List (Local.Symbol machine) →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
plainSymbols [] = []
plainSymbols (symbol ∷ rest) =
  Local.plain symbol ∷ plainSymbols rest

plainSymbolsArePlain :
  ∀ {machine}
    (symbols : List (Local.Symbol machine)) →
  WF.PlainCells (plainSymbols {machine} symbols)
plainSymbolsArePlain [] =
  WF.plainNil
plainSymbolsArePlain (symbol ∷ rest) =
  WF.plainCons (plainSymbolsArePlain rest)

appendPlainBlank :
  ∀ {machine} →
  List (Local.Symbol machine) →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
appendPlainBlank {machine} symbols =
  Local.append
    (plainSymbols symbols)
    (Local.plain (Local.blank machine) ∷ [])

appendPlainBlankArePlain :
  ∀ {machine}
    (symbols : List (Local.Symbol machine)) →
  WF.PlainCells (appendPlainBlank {machine} symbols)
appendPlainBlankArePlain [] =
  WF.plainCons WF.plainNil
appendPlainBlankArePlain (symbol ∷ rest) =
  WF.plainCons (appendPlainBlankArePlain rest)

inputHeadSymbol :
  ∀ {machine} →
  InputWord machine →
  Local.Symbol machine
inputHeadSymbol {machine} [] =
  Local.blank machine
inputHeadSymbol (symbol ∷ rest) =
  symbol

inputTail :
  ∀ {machine} →
  InputWord machine →
  List (Local.Symbol machine)
inputTail [] = []
inputTail (symbol ∷ rest) = rest

initialInputCells :
  ∀ {machine} →
  InputWord machine →
  List
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
initialInputCells {machine} input =
  Local.plain (Local.blank machine)
  ∷ Local.headed
      (Local.initialState machine)
      (inputHeadSymbol input)
  ∷ Local.plain rightSymbol
  ∷ suffix
  where
    tail = inputTail input

    rightSymbol : Local.Symbol machine
    rightSymbol with tail
    ... | [] = Local.blank machine
    ... | symbol ∷ rest = symbol

    suffix :
      List
        (Local.TapeCell
          (Local.State machine)
          (Local.Symbol machine))
    suffix with tail
    ... | [] = []
    ... | symbol ∷ rest =
      appendPlainBlank rest

initialInputRow :
  ∀ {machine} →
  InputWord machine →
  Local.TapeRow machine
initialInputRow input =
  Local.tape-row (initialInputCells input)

initialInputInterior :
  ∀ {machine}
    (input : InputWord machine) →
  Locality.InteriorHeadConfiguration
    machine
    (initialInputRow input)
initialInputInterior {machine} [] = record
  { Locality.prefix = []
  ; Locality.suffix = []
  ; Locality.leftSymbol = Local.blank machine
  ; Locality.readSymbol = Local.blank machine
  ; Locality.rightSymbol = Local.blank machine
  ; Locality.headState = Local.initialState machine
  ; Locality.prefixPlain = WF.plainNil
  ; Locality.suffixPlain = WF.plainNil
  ; Locality.rowShape = refl
  }
initialInputInterior {machine} (symbol ∷ []) = record
  { Locality.prefix = []
  ; Locality.suffix = []
  ; Locality.leftSymbol = Local.blank machine
  ; Locality.readSymbol = symbol
  ; Locality.rightSymbol = Local.blank machine
  ; Locality.headState = Local.initialState machine
  ; Locality.prefixPlain = WF.plainNil
  ; Locality.suffixPlain = WF.plainNil
  ; Locality.rowShape = refl
  }
initialInputInterior {machine}
    (symbol ∷ next ∷ rest) = record
  { Locality.prefix = []
  ; Locality.suffix = appendPlainBlank rest
  ; Locality.leftSymbol = Local.blank machine
  ; Locality.readSymbol = symbol
  ; Locality.rightSymbol = next
  ; Locality.headState = Local.initialState machine
  ; Locality.prefixPlain = WF.plainNil
  ; Locality.suffixPlain = appendPlainBlankArePlain rest
  ; Locality.rowShape = refl
  }

initialInputIsInitialInterior :
  ∀ {machine}
    (input : InputWord machine) →
  Accepting.InitialInteriorRow
    machine
    (initialInputRow input)
initialInputIsInitialInterior input = record
  { Accepting.interior = initialInputInterior input
  ; Accepting.headIsInitial = refl
  }

inputPayloadLength :
  ∀ {machine} →
  InputWord machine →
  Nat
inputPayloadLength input =
  Canonical.listLength input

initialInputCellCount :
  ∀ {machine}
    (input : InputWord machine) →
  Nat
initialInputCellCount input =
  Canonical.listLength (initialInputCells input)

initialInputCellCount_nonempty :
  ∀ {machine}
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine)) →
  initialInputCellCount (symbol ∷ rest)
  ≡ suc (suc (Canonical.listLength rest))
initialInputCellCount_nonempty symbol [] = refl
initialInputCellCount_nonempty symbol (next ∷ rest) = refl

record InputInitialRowReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    inputWordCarrierPaid : Bool
    literalInputInitialRowPaid : Bool
    inputHeadInitialStatePaid : Bool
    inputSymbolsEmbeddedInInitialRowPaid : Bool
    leftRightBoundaryBlankPaid : Bool
    interiorHeadConventionPaid : Bool
    fixedPolynomialPaddingPaid : Bool
    initialRowCNFPlacementPaid : Bool
    acceptingRowCNFPlacementPaid : Bool
    acceptingAssignmentIffRunPaid : Bool
    polynomialReductionPaid : Bool
    pVsNPResolved : Bool

canonicalInputInitialRowReceipt :
  ∀ (machine : Local.ConcreteTapeMachine) →
  InputInitialRowReceipt machine
canonicalInputInitialRowReceipt machine = record
  { inputWordCarrierPaid = true
  ; literalInputInitialRowPaid = true
  ; inputHeadInitialStatePaid = true
  ; inputSymbolsEmbeddedInInitialRowPaid = true
  ; leftRightBoundaryBlankPaid = true
  ; interiorHeadConventionPaid = true
  ; fixedPolynomialPaddingPaid = false
  ; initialRowCNFPlacementPaid = false
  ; acceptingRowCNFPlacementPaid = false
  ; acceptingAssignmentIffRunPaid = false
  ; polynomialReductionPaid = false
  ; pVsNPResolved = false
  }
