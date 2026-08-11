module DASHI.Physics.Closure.NSTriadKNLuoFiniteKernelCommutatorRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
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
-- DASHI CONTRIBUTION
--
-- Before invoking any continuum Calderon-Zygmund theorem, this file proves the
-- exact finite-kernel commutator identity cell by cell:
--
--   w a(x-y) grad b(x-y) - a(x) w grad b(x-y)
--     = w (a(x-y)-a(x)) grad b(x-y).
--
-- It then proves exact recomposition over a finite kernel and the first-moment
-- scaling law under literal distance rescaling.  The analytic estimate from
-- the increment to ||grad a||_infinity remains a separate continuum producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

zeroQ : ℚ
zeroQ = Int.+ 0 / 1

record FiniteKernelTransportCell : Set where
  constructor finite-kernel-transport-cell
  field
    weight : ℚ
    shiftedAdvectingValue : ℚ
    baseAdvectingValue : ℚ
    shiftedGradientValue : ℚ

open FiniteKernelTransportCell public

filteredTransportCell : FiniteKernelTransportCell → ℚ
filteredTransportCell C =
  weight C * shiftedAdvectingValue C * shiftedGradientValue C

transportOfFilteredCell : FiniteKernelTransportCell → ℚ
transportOfFilteredCell C =
  baseAdvectingValue C * (weight C * shiftedGradientValue C)

commutatorCell : FiniteKernelTransportCell → ℚ
commutatorCell C =
  filteredTransportCell C - transportOfFilteredCell C

incrementCell : FiniteKernelTransportCell → ℚ
incrementCell C =
  weight C
  * (shiftedAdvectingValue C - baseAdvectingValue C)
  * shiftedGradientValue C

finiteKernelCommutatorCellIdentity :
  (C : FiniteKernelTransportCell) →
  commutatorCell C ≡ incrementCell C
finiteKernelCommutatorCellIdentity C =
  solve
    ( weight C
    ∷ shiftedAdvectingValue C
    ∷ baseAdvectingValue C
    ∷ shiftedGradientValue C
    ∷ [])

sumCommutatorCells : List FiniteKernelTransportCell → ℚ
sumCommutatorCells [] = zeroQ
sumCommutatorCells (C ∷ rest) =
  commutatorCell C + sumCommutatorCells rest

sumIncrementCells : List FiniteKernelTransportCell → ℚ
sumIncrementCells [] = zeroQ
sumIncrementCells (C ∷ rest) =
  incrementCell C + sumIncrementCells rest

finiteKernelCommutatorIdentity :
  (cells : List FiniteKernelTransportCell) →
  sumCommutatorCells cells ≡ sumIncrementCells cells
finiteKernelCommutatorIdentity [] = refl
finiteKernelCommutatorIdentity (C ∷ rest)
  rewrite finiteKernelCommutatorCellIdentity C
        | finiteKernelCommutatorIdentity rest = refl

------------------------------------------------------------------------
-- Exact finite first-moment scaling.
------------------------------------------------------------------------

record FiniteKernelMomentCell : Set where
  constructor finite-kernel-moment-cell
  field
    momentWeight : ℚ
    displacementSize : ℚ

open FiniteKernelMomentCell public

scaleMomentCell : ℚ → FiniteKernelMomentCell → FiniteKernelMomentCell
scaleMomentCell scale C =
  finite-kernel-moment-cell
    (momentWeight C)
    (scale * displacementSize C)

scaleMomentCells :
  ℚ → List FiniteKernelMomentCell → List FiniteKernelMomentCell
scaleMomentCells scale [] = []
scaleMomentCells scale (C ∷ rest) =
  scaleMomentCell scale C ∷ scaleMomentCells scale rest

firstMoment : List FiniteKernelMomentCell → ℚ
firstMoment [] = zeroQ
firstMoment (C ∷ rest) =
  momentWeight C * displacementSize C + firstMoment rest

firstMomentScaleLaw :
  (scale : ℚ) →
  (cells : List FiniteKernelMomentCell) →
  firstMoment (scaleMomentCells scale cells)
  ≡ scale * firstMoment cells
firstMomentScaleLaw scale [] = solve []
firstMomentScaleLaw scale (C ∷ rest)
  rewrite firstMomentScaleLaw scale rest =
  solve
    ( scale
    ∷ momentWeight C
    ∷ displacementSize C
    ∷ firstMoment rest
    ∷ [])

record DyadicFirstMomentWitness : Set where
  constructor dyadic-first-moment-witness
  field
    inverseScale : ℚ
    motherCells : List FiniteKernelMomentCell
    shellCells : List FiniteKernelMomentCell
    shellCellsMeaning :
      shellCells ≡ scaleMomentCells inverseScale motherCells

open DyadicFirstMomentWitness public

dyadicFirstMomentInherited :
  (W : DyadicFirstMomentWitness) →
  firstMoment (shellCells W)
  ≡ inverseScale W * firstMoment (motherCells W)
dyadicFirstMomentInherited W
  rewrite shellCellsMeaning W =
  firstMomentScaleLaw (inverseScale W) (motherCells W)
