module DASHI.Physics.Closure.NSTriadKNFiniteHermitianDiagonalMultiplierExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove, by finite recursion only, that a real 0/1 diagonal Fourier
-- multiplier is self-adjoint for any Hermitian coefficient pairing.  The
-- coefficient field is represented by `Maybe`: `nothing` is the zero
-- coefficient and `just value` is an occupied Fourier mode.  No Parseval,
-- completeness or unbounded-operator theorem occurs in this file.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)

record FiniteHermitianPairing
    {c s : Level}
    (Coefficient : Set c)
    (Scalar : Set s) : Set (lsuc (c ⊔ s)) where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    pair : Coefficient → Coefficient → Scalar

open FiniteHermitianPairing public

maybePair :
  ∀ {c s} {Coefficient : Set c} {Scalar : Set s} →
  FiniteHermitianPairing Coefficient Scalar →
  Maybe Coefficient → Maybe Coefficient → Scalar
maybePair P nothing right = zero P
maybePair P (just left) nothing = zero P
maybePair P (just left) (just right) = pair P left right

diagonalProject :
  ∀ {c} {Coefficient : Set c} →
  Bool → Maybe Coefficient → Maybe Coefficient
diagonalProject true coefficient = coefficient
diagonalProject false coefficient = nothing

diagonalProjectIdempotent :
  ∀ {c} {Coefficient : Set c} →
  (selected : Bool) →
  (coefficient : Maybe Coefficient) →
  diagonalProject selected (diagonalProject selected coefficient)
    ≡ diagonalProject selected coefficient
diagonalProjectIdempotent true coefficient = refl
diagonalProjectIdempotent false coefficient = refl

diagonalTermSelfAdjoint :
  ∀ {c s} {Coefficient : Set c} {Scalar : Set s} →
  (P : FiniteHermitianPairing Coefficient Scalar) →
  (selected : Bool) →
  (left right : Maybe Coefficient) →
  maybePair P (diagonalProject selected left) right
    ≡ maybePair P left (diagonalProject selected right)
diagonalTermSelfAdjoint P true left right = refl
diagonalTermSelfAdjoint P false nothing right = refl
diagonalTermSelfAdjoint P false (just left) right = refl

finiteHermitianPairing :
  ∀ {i c s}
    {Index : Set i}
    {Coefficient : Set c}
    {Scalar : Set s} →
  FiniteHermitianPairing Coefficient Scalar →
  List Index →
  (Index → Maybe Coefficient) →
  (Index → Maybe Coefficient) →
  Scalar
finiteHermitianPairing P [] left right = zero P
finiteHermitianPairing P (index ∷ indices) left right =
  add P
    (maybePair P (left index) (right index))
    (finiteHermitianPairing P indices left right)

diagonalField :
  ∀ {i c}
    {Index : Set i}
    {Coefficient : Set c} →
  (Index → Bool) →
  (Index → Maybe Coefficient) →
  Index → Maybe Coefficient
diagonalField selected field index =
  diagonalProject (selected index) (field index)

finiteDiagonalMultiplierSelfAdjoint :
  ∀ {i c s}
    {Index : Set i}
    {Coefficient : Set c}
    {Scalar : Set s} →
  (P : FiniteHermitianPairing Coefficient Scalar) →
  (indices : List Index) →
  (selected : Index → Bool) →
  (left right : Index → Maybe Coefficient) →
  finiteHermitianPairing P indices
    (diagonalField selected left) right
    ≡
  finiteHermitianPairing P indices
    left (diagonalField selected right)
finiteDiagonalMultiplierSelfAdjoint P [] selected left right = refl
finiteDiagonalMultiplierSelfAdjoint
  P (index ∷ indices) selected left right
  rewrite diagonalTermSelfAdjoint
    P (selected index) (left index) (right index)
        | finiteDiagonalMultiplierSelfAdjoint
            P indices selected left right = refl

finiteDiagonalMultiplierIdempotent :
  ∀ {i c}
    {Index : Set i}
    {Coefficient : Set c} →
  (indices : List Index) →
  (selected : Index → Bool) →
  (field : Index → Maybe Coefficient) →
  (index : Index) →
  diagonalField selected (diagonalField selected field) index
    ≡ diagonalField selected field index
finiteDiagonalMultiplierIdempotent indices selected field index =
  diagonalProjectIdempotent (selected index) (field index)

finiteHermitianDiagonalSelfAdjointnessConstructed : Bool
finiteHermitianDiagonalSelfAdjointnessConstructed = true

finiteHermitianDiagonalIdempotenceConstructed : Bool
finiteHermitianDiagonalIdempotenceConstructed = true

finiteHermitianDiagonalSelfAdjointnessConstructedIsTrue :
  finiteHermitianDiagonalSelfAdjointnessConstructed ≡ true
finiteHermitianDiagonalSelfAdjointnessConstructedIsTrue = refl

finiteHermitianDiagonalIdempotenceConstructedIsTrue :
  finiteHermitianDiagonalIdempotenceConstructed ≡ true
finiteHermitianDiagonalIdempotenceConstructedIsTrue = refl
