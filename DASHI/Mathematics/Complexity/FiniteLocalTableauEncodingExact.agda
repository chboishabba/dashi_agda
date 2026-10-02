module DASHI.Mathematics.Complexity.FiniteLocalTableauEncodingExact where

------------------------------------------------------------------------
-- FINITE LOCAL TABLEAU REPRESENTATION
--
-- Cook--Levin needs more than an abstract Configuration : Set.  This owner
-- supplies the missing representation layer without yet claiming CNF:
--
--   * every cell has a fixed-width Boolean code;
--   * rows and tableaux carry exact finite dimensions;
--   * flattening a row has exactly space * cellWidth bits;
--   * flattening a tableau has exactly time * space * cellWidth bits;
--   * local legality is an explicit finite Boolean predicate.
--
-- The final CNF theorem must compile the supplied local predicate plus initial
-- and accepting predicates into clauses.  That is now a sharply typed next
-- seam rather than an arbitrary-Set encoding problem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

lengthAppend :
  ∀ {A : Set} (xs ys : List A) →
  listLength (append xs ys) ≡ listLength xs + listLength ys
lengthAppend [] ys = refl
lengthAppend (x ∷ xs) ys =
  cong suc (lengthAppend xs ys)

record FixedWidthCellCode : Set₁ where
  field
    Cell : Set
    cellWidth : Nat
    encodeCell : Cell → List Bool
    decodeCell : List Bool → Cell

    encodedCellWidth :
      (cell : Cell) →
      listLength (encodeCell cell) ≡ cellWidth

    decodeEncodeCell :
      (cell : Cell) →
      decodeCell (encodeCell cell) ≡ cell

open FixedWidthCellCode public

encodeCells :
  (code : FixedWidthCellCode) →
  List (Cell code) →
  List Bool
encodeCells code [] = []
encodeCells code (cell ∷ cells) =
  append (encodeCell code cell) (encodeCells code cells)

encodedCellsLength :
  (code : FixedWidthCellCode) →
  (cells : List (Cell code)) →
  listLength (encodeCells code cells)
  ≡ listLength cells * cellWidth code
encodedCellsLength code [] = refl
encodedCellsLength code (cell ∷ cells) =
  trans
    (lengthAppend
      (encodeCell code cell)
      (encodeCells code cells))
    (trans
      (cong
        (λ n → n + listLength (encodeCells code cells))
        (encodedCellWidth code cell))
      (trans
        (cong
          (λ n → cellWidth code + n)
          (encodedCellsLength code cells))
        (sym
          (sucTimes
            (listLength cells)
            (cellWidth code)))))
  where
    trans : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

    sucTimes : ∀ n w →
      suc n * w ≡ w + n * w
    sucTimes n w = refl

record FixedWidthRow
    (code : FixedWidthCellCode)
    (space : Nat) : Set₁ where
  constructor fixed-width-row
  field
    cells : List (Cell code)
    exactSpace : listLength cells ≡ space

open FixedWidthRow public

encodeRow :
  ∀ {code space} →
  FixedWidthRow code space →
  List Bool
encodeRow {code = code} row =
  encodeCells code (cells row)

encodedRowLength :
  ∀ {code space}
    (row : FixedWidthRow code space) →
  listLength (encodeRow row)
  ≡ space * cellWidth code
encodedRowLength {code = code} {space = space} row =
  trans
    (encodedCellsLength code (cells row))
    (cong (λ n → n * cellWidth code) (exactSpace row))
  where
    trans : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

record FiniteTableau
    (code : FixedWidthCellCode)
    (time space : Nat) : Set₁ where
  constructor finite-tableau
  field
    rows : List (FixedWidthRow code space)
    exactTime : listLength rows ≡ time

open FiniteTableau public

encodeRows :
  ∀ {code space} →
  List (FixedWidthRow code space) →
  List Bool
encodeRows [] = []
encodeRows (row ∷ rest) =
  append (encodeRow row) (encodeRows rest)

encodedRowsLength :
  ∀ {code space}
    (rows : List (FixedWidthRow code space)) →
  listLength (encodeRows rows)
  ≡ listLength rows * (space * cellWidth code)
encodedRowsLength {code = code} {space = space} [] = refl
encodedRowsLength {code = code} {space = space} (row ∷ rest) =
  trans
    (lengthAppend (encodeRow row) (encodeRows rest))
    (trans
      (cong
        (λ n → n + listLength (encodeRows rest))
        (encodedRowLength row))
      (trans
        (cong
          (λ n → (space * cellWidth code) + n)
          (encodedRowsLength rest))
        (sym
          (sucTimes
            (listLength rest)
            (space * cellWidth code)))))
  where
    trans : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

    sucTimes : ∀ n w →
      suc n * w ≡ w + n * w
    sucTimes n w = refl

encodeTableau :
  ∀ {code time space} →
  FiniteTableau code time space →
  List Bool
encodeTableau tableau =
  encodeRows (rows tableau)

encodedTableauLength :
  ∀ {code time space}
    (tableau : FiniteTableau code time space) →
  listLength (encodeTableau tableau)
  ≡ time * (space * cellWidth code)
encodedTableauLength {code = code} {time = time} {space = space} tableau =
  trans
    (encodedRowsLength (rows tableau))
    (cong
      (λ n → n * (space * cellWidth code))
      (exactTime tableau))
  where
    trans : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    trans refl second = second

record LocalTableauPredicates
    (code : FixedWidthCellCode) : Set₁ where
  field
    initialCellAllowed : Cell code → Bool
    acceptingCell : Cell code → Bool

    -- A 2x3 window is enough to type the usual one-tape local transition
    -- check while remaining independent of one particular TM convention.
    localWindowAllowed :
      Cell code → Cell code → Cell code →
      Cell code → Cell code → Cell code →
      Bool

open LocalTableauPredicates public

record CookLevinFiniteRepresentation
    (code : FixedWidthCellCode) : Set₁ where
  field
    predicates : LocalTableauPredicates code
    timeBound : Nat → Nat
    spaceBound : Nat → Nat
    timePolynomial : ERQ.PolynomialBound timeBound
    spacePolynomial : ERQ.PolynomialBound spaceBound

open CookLevinFiniteRepresentation public
