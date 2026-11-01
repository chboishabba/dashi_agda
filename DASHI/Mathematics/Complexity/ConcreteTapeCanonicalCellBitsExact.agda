module DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact where

------------------------------------------------------------------------
-- CANONICAL CONCRETE TAPE CELL <-> FIXED-WIDTH BITS
--
-- The existing ConcreteTapeMachine finite enumeration record carries a list
-- and decidable equality, but its abstract "occurs" field is not connected to
-- list membership.  The minimal extra witness below states exactly that the
-- advertised enumeration list really contains every value.
--
-- From that witness we compile:
--
--   State  <-> Bits |states|
--   Symbol <-> Bits |symbols|
--   TapeCell <-> Bits (1 + |states| + |symbols|)
--   SixCellWindow <-> Bits (6 * cellWidth)
--
-- and then instantiate the existing FixedWidthWindowCodec consumed by the
-- truth-table-CNF machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.ConcreteTapeWindowCodecCNFWeldExact as Window

------------------------------------------------------------------------
-- Lists and genuine enumeration coverage
------------------------------------------------------------------------

data Member {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → Member x (x ∷ xs)
  there : ∀ {y xs} → Member x xs → Member x (y ∷ xs)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

record EnumerationCoverage {A : Set}
    (enumeration : Local.FiniteEnumeration A) : Set₁ where
  field
    listed : (x : A) → Member x (Local.values enumeration)

open EnumerationCoverage public

------------------------------------------------------------------------
-- Canonical one-hot finite-value codec
------------------------------------------------------------------------

record FixedBitsCodec (A : Set) (width : Nat) : Set₁ where
  field
    encode : A → CNF.Bits width
    decode : CNF.Bits width → A
    decodeEncode : (x : A) → decode (encode x) ≡ x

open FixedBitsCodec public

encodeAgainst :
  ∀ {A : Set}
    (decide : A → A → Bool) →
  A →
  (xs : List A) →
  CNF.Bits (listLength xs)
encodeAgainst decide x [] = CNF.[]ᵇ
encodeAgainst decide x (y ∷ ys) =
  decide x y CNF.∷ᵇ encodeAgainst decide x ys

decodeAgainst :
  ∀ {A : Set} →
  A →
  (xs : List A) →
  CNF.Bits (listLength xs) →
  A
decodeAgainst fallback [] CNF.[]ᵇ = fallback
decodeAgainst fallback (x ∷ xs) (false CNF.∷ᵇ bits) =
  decodeAgainst fallback xs bits
decodeAgainst fallback (x ∷ xs) (true CNF.∷ᵇ bits) =
  x

decodeEncodeAgainst :
  ∀ {A : Set}
    (enumeration : Local.FiniteEnumeration A)
    (fallback x : A)
    (xs : List A) →
  Member x xs →
  decodeAgainst fallback xs
    (encodeAgainst (Local.decideEqual enumeration) x xs)
  ≡ x
decodeEncodeAgainst enumeration fallback x .(x ∷ xs) (here {xs})
    rewrite Local.decideEqualRefl enumeration x =
  refl
decodeEncodeAgainst enumeration fallback x (y ∷ ys) (there membership)
    with Local.decideEqual enumeration x y
... | false =
  decodeEncodeAgainst enumeration fallback x ys membership
... | true
    with Local.decideEqualSound enumeration {x} {y} refl
... | refl = refl

canonicalFiniteCodec :
  ∀ {A : Set}
    (enumeration : Local.FiniteEnumeration A)
    (coverage : EnumerationCoverage enumeration)
    (fallback : A) →
  FixedBitsCodec A (listLength (Local.values enumeration))
canonicalFiniteCodec enumeration coverage fallback = record
  { encode =
      λ x →
        encodeAgainst
          (Local.decideEqual enumeration)
          x
          (Local.values enumeration)
  ; decode =
      decodeAgainst fallback (Local.values enumeration)
  ; decodeEncode =
      λ x →
        decodeEncodeAgainst
          enumeration fallback x
          (Local.values enumeration)
          (listed coverage x)
  }

------------------------------------------------------------------------
-- Bit concatenation / splitting
------------------------------------------------------------------------

appendBits :
  ∀ {m n : Nat} →
  CNF.Bits m →
  CNF.Bits n →
  CNF.Bits (m + n)
appendBits CNF.[]ᵇ right = right
appendBits (bit CNF.∷ᵇ left) right =
  bit CNF.∷ᵇ appendBits left right

takeBits :
  ∀ (m : Nat) {n : Nat} →
  CNF.Bits (m + n) →
  CNF.Bits m
takeBits zero bits = CNF.[]ᵇ
takeBits (suc m) (bit CNF.∷ᵇ bits) =
  bit CNF.∷ᵇ takeBits m bits

dropBits :
  ∀ (m : Nat) {n : Nat} →
  CNF.Bits (m + n) →
  CNF.Bits n
dropBits zero bits = bits
dropBits (suc m) (bit CNF.∷ᵇ bits) =
  dropBits m bits

takeAppendBits :
  ∀ {m n : Nat}
    (left : CNF.Bits m)
    (right : CNF.Bits n) →
  takeBits m (appendBits left right) ≡ left
takeAppendBits CNF.[]ᵇ right = refl
takeAppendBits (bit CNF.∷ᵇ left) right
    rewrite takeAppendBits left right =
  refl

dropAppendBits :
  ∀ {m n : Nat}
    (left : CNF.Bits m)
    (right : CNF.Bits n) →
  dropBits m (appendBits left right) ≡ right
dropAppendBits CNF.[]ᵇ right = refl
dropAppendBits (bit CNF.∷ᵇ left) right =
  dropAppendBits left right

pairCodec :
  ∀ {A B : Set} {m n : Nat} →
  FixedBitsCodec A m →
  FixedBitsCodec B n →
  FixedBitsCodec (A × B) (m + n)
pairCodec {m = m} left right = record
  { encode =
      λ pair →
        appendBits
          (encode left (fst pair))
          (encode right (snd pair))
  ; decode =
      λ bits →
        decode left (takeBits m bits) ,
        decode right (dropBits m bits)
  ; decodeEncode =
      λ pair →
        pairDecodeEncode pair
  }
  where
    fst : ∀ {X Y : Set} → X × Y → X
    fst (x , y) = x

    snd : ∀ {X Y : Set} → X × Y → Y
    snd (x , y) = y

    pairDecodeEncode :
      (pair : A × B) →
      ( decode left
          (takeBits m
            (appendBits
              (encode left (fst pair))
              (encode right (snd pair))))
      , decode right
          (dropBits m
            (appendBits
              (encode left (fst pair))
              (encode right (snd pair))))
      )
      ≡ pair
    pairDecodeEncode (x , y)
      rewrite takeAppendBits (encode left x) (encode right y)
            | dropAppendBits (encode left x) (encode right y)
            | decodeEncode left x
            | decodeEncode right y =
      refl

------------------------------------------------------------------------
-- Concrete machine State / Symbol / TapeCell codecs
------------------------------------------------------------------------

StateWidth : Local.ConcreteTapeMachine → Nat
StateWidth machine =
  listLength (Local.values (Local.finiteState machine))

SymbolWidth : Local.ConcreteTapeMachine → Nat
SymbolWidth machine =
  listLength (Local.values (Local.finiteSymbol machine))

CellWidth : Local.ConcreteTapeMachine → Nat
CellWidth machine =
  suc (StateWidth machine + SymbolWidth machine)

canonicalStateCodec :
  ∀ (machine : Local.ConcreteTapeMachine) →
  EnumerationCoverage (Local.finiteState machine) →
  FixedBitsCodec
    (Local.State machine)
    (StateWidth machine)
canonicalStateCodec machine coverage =
  canonicalFiniteCodec
    (Local.finiteState machine)
    coverage
    (Local.initialState machine)

canonicalSymbolCodec :
  ∀ (machine : Local.ConcreteTapeMachine) →
  EnumerationCoverage (Local.finiteSymbol machine) →
  FixedBitsCodec
    (Local.Symbol machine)
    (SymbolWidth machine)
canonicalSymbolCodec machine coverage =
  canonicalFiniteCodec
    (Local.finiteSymbol machine)
    coverage
    (Local.blank machine)

encodeCell :
  ∀ {machine}
    (stateCoverage :
      EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      EnumerationCoverage (Local.finiteSymbol machine)) →
  Local.TapeCell
    (Local.State machine)
    (Local.Symbol machine) →
  CNF.Bits (CellWidth machine)
encodeCell {machine} stateCoverage symbolCoverage
    (Local.plain symbol) =
  false CNF.∷ᵇ
    appendBits
      (encode
        (canonicalStateCodec machine stateCoverage)
        (Local.initialState machine))
      (encode
        (canonicalSymbolCodec machine symbolCoverage)
        symbol)
encodeCell {machine} stateCoverage symbolCoverage
    (Local.headed state symbol) =
  true CNF.∷ᵇ
    appendBits
      (encode
        (canonicalStateCodec machine stateCoverage)
        state)
      (encode
        (canonicalSymbolCodec machine symbolCoverage)
        symbol)

decodeCell :
  ∀ {machine}
    (stateCoverage :
      EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      EnumerationCoverage (Local.finiteSymbol machine)) →
  CNF.Bits (CellWidth machine) →
  Local.TapeCell
    (Local.State machine)
    (Local.Symbol machine)
decodeCell {machine} stateCoverage symbolCoverage
    (false CNF.∷ᵇ payload) =
  Local.plain
    (decode
      (canonicalSymbolCodec machine symbolCoverage)
      (dropBits (StateWidth machine) payload))
decodeCell {machine} stateCoverage symbolCoverage
    (true CNF.∷ᵇ payload) =
  Local.headed
    (decode
      (canonicalStateCodec machine stateCoverage)
      (takeBits (StateWidth machine) payload))
    (decode
      (canonicalSymbolCodec machine symbolCoverage)
      (dropBits (StateWidth machine) payload))

decodeEncodeCell :
  ∀ {machine}
    (stateCoverage :
      EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      EnumerationCoverage (Local.finiteSymbol machine))
    (cell :
      Local.TapeCell
        (Local.State machine)
        (Local.Symbol machine)) →
  decodeCell stateCoverage symbolCoverage
    (encodeCell stateCoverage symbolCoverage cell)
  ≡ cell
decodeEncodeCell {machine} stateCoverage symbolCoverage
    (Local.plain symbol)
    rewrite dropAppendBits
      (encode
        (canonicalStateCodec machine stateCoverage)
        (Local.initialState machine))
      (encode
        (canonicalSymbolCodec machine symbolCoverage)
        symbol)
          | decodeEncode
              (canonicalSymbolCodec machine symbolCoverage)
              symbol =
  refl
decodeEncodeCell {machine} stateCoverage symbolCoverage
    (Local.headed state symbol)
    rewrite takeAppendBits
      (encode
        (canonicalStateCodec machine stateCoverage)
        state)
      (encode
        (canonicalSymbolCodec machine symbolCoverage)
        symbol)
          | dropAppendBits
              (encode
                (canonicalStateCodec machine stateCoverage)
                state)
              (encode
                (canonicalSymbolCodec machine symbolCoverage)
                symbol)
          | decodeEncode
              (canonicalStateCodec machine stateCoverage)
              state
          | decodeEncode
              (canonicalSymbolCodec machine symbolCoverage)
              symbol =
  refl

canonicalCellCodec :
  ∀ (machine : Local.ConcreteTapeMachine) →
  EnumerationCoverage (Local.finiteState machine) →
  EnumerationCoverage (Local.finiteSymbol machine) →
  FixedBitsCodec
    (Local.TapeCell
      (Local.State machine)
      (Local.Symbol machine))
    (CellWidth machine)
canonicalCellCodec machine stateCoverage symbolCoverage = record
  { encode = encodeCell stateCoverage symbolCoverage
  ; decode = decodeCell stateCoverage symbolCoverage
  ; decodeEncode = decodeEncodeCell stateCoverage symbolCoverage
  }

------------------------------------------------------------------------
-- Six-cell codec, using six literal copies of the canonical cell code
------------------------------------------------------------------------

WindowWidth : Local.ConcreteTapeMachine → Nat
WindowWidth machine =
  CellWidth machine +
  (CellWidth machine +
  (CellWidth machine +
  (CellWidth machine +
  (CellWidth machine +
   CellWidth machine))))

WindowTuple :
  (machine : Local.ConcreteTapeMachine) → Set
WindowTuple machine =
  Local.TapeCell (Local.State machine) (Local.Symbol machine) ×
  (Local.TapeCell (Local.State machine) (Local.Symbol machine) ×
  (Local.TapeCell (Local.State machine) (Local.Symbol machine) ×
  (Local.TapeCell (Local.State machine) (Local.Symbol machine) ×
  (Local.TapeCell (Local.State machine) (Local.Symbol machine) ×
   Local.TapeCell (Local.State machine) (Local.Symbol machine)))))

windowToTuple :
  ∀ {machine} →
  Local.SixCellWindow machine →
  WindowTuple machine
windowToTuple window =
  Local.oldLeft window ,
  (Local.oldCenter window ,
  (Local.oldRight window ,
  (Local.newLeft window ,
  (Local.newCenter window ,
   Local.newRight window))))

tupleToWindow :
  ∀ {machine} →
  WindowTuple machine →
  Local.SixCellWindow machine
tupleToWindow
    (oldLeft ,
    (oldCenter ,
    (oldRight ,
    (newLeft ,
    (newCenter , newRight))))) =
  Local.six-cell-window
    oldLeft oldCenter oldRight
    newLeft newCenter newRight

tupleWindowRoundTrip :
  ∀ {machine}
    (window : Local.SixCellWindow machine) →
  tupleToWindow (windowToTuple window) ≡ window
tupleWindowRoundTrip
    (Local.six-cell-window
      oldLeft oldCenter oldRight
      newLeft newCenter newRight) =
  refl

canonicalWindowTupleCodec :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      EnumerationCoverage (Local.finiteSymbol machine)) →
  FixedBitsCodec
    (WindowTuple machine)
    (WindowWidth machine)
canonicalWindowTupleCodec machine stateCoverage symbolCoverage =
  pairCodec cell
    (pairCodec cell
      (pairCodec cell
        (pairCodec cell
          (pairCodec cell cell))))
  where
    cell = canonicalCellCodec machine stateCoverage symbolCoverage

canonicalWindowCodec :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      EnumerationCoverage (Local.finiteSymbol machine)) →
  Window.FixedWidthWindowCodec
    machine
    (WindowWidth machine)
canonicalWindowCodec machine stateCoverage symbolCoverage = record
  { Window.encode =
      λ window →
        encode tupleCodec (windowToTuple window)
  ; Window.decode =
      λ bits →
        tupleToWindow (decode tupleCodec bits)
  ; Window.decodeEncode =
      λ window →
        trans
          (cong tupleToWindow
            (decodeEncode tupleCodec (windowToTuple window)))
          (tupleWindowRoundTrip window)
  }
  where
    tupleCodec =
      canonicalWindowTupleCodec
        machine stateCoverage symbolCoverage

    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

record CanonicalConcreteCellBitsReceipt
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    stateEnumerationListsEveryValue :
      EnumerationCoverage (Local.finiteState machine)
    symbolEnumerationListsEveryValue :
      EnumerationCoverage (Local.finiteSymbol machine)

    stateWidth : Nat
    symbolWidth : Nat
    cellWidth : Nat
    windowWidth : Nat

    stateWidthExact : stateWidth ≡ StateWidth machine
    symbolWidthExact : symbolWidth ≡ SymbolWidth machine
    cellWidthExact : cellWidth ≡ CellWidth machine
    windowWidthExact : windowWidth ≡ WindowWidth machine

canonicalConcreteCellBitsReceipt :
  ∀ (machine : Local.ConcreteTapeMachine)
    (stateCoverage :
      EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      EnumerationCoverage (Local.finiteSymbol machine)) →
  CanonicalConcreteCellBitsReceipt machine
canonicalConcreteCellBitsReceipt machine stateCoverage symbolCoverage = record
  { stateEnumerationListsEveryValue = stateCoverage
  ; symbolEnumerationListsEveryValue = symbolCoverage
  ; stateWidth = StateWidth machine
  ; symbolWidth = SymbolWidth machine
  ; cellWidth = CellWidth machine
  ; windowWidth = WindowWidth machine
  ; stateWidthExact = refl
  ; symbolWidthExact = refl
  ; cellWidthExact = refl
  ; windowWidthExact = refl
  }
