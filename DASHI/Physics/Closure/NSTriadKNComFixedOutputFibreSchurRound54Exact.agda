module DASHI.Physics.Closure.NSTriadKNComFixedOutputFibreSchurRound54Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column matrix norm test; no DOI assigned to the original
-- theorem.
--
-- Roger A. Horn; Charles R. Johnson.
-- Title: "Matrix Analysis", second edition.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- The remaining Com difficulty is not incidence counting.  For a FIXED output
-- Fourier mode k all resonant inputs contributing to k must be treated as one
-- coherent fibre.  This file imports the repository's already machine-checked
-- rectangular Schur theorem and specializes it to one fixed output row.
--
-- If the whole absolute fibre mass is <= R and every individual column mass is
-- <= C, then for every input vector
--
--   |sum_j K(k,j) f_j|^2 <= R C sum_j |f_j|^2.
--
-- Thus a proof of the physical same/adjacent constants should target the WHOLE
-- fixed-output absolute fibre sum.  No number-of-triads factor appears after
-- that sum is bounded.  This is the concrete finite convolution/Schur engine
-- requested by the Round-54 audit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as Rect
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record FixedOutputFourierFibre (Column : Set) : Set₁ where
  field
    columns : List Column
    kernel : Column → ℚ
    rowBound columnBound : ℚ

    rowBoundNonnegative : 0ℚ ≤ rowBound
    columnBoundNonnegative : 0ℚ ≤ columnBound

    wholeAbsoluteFibreMassBound :
      Sums.sumRational columns (λ column → ∣ kernel column ∣)
      ≤ rowBound

    everyColumnMassBound : ∀ column →
      ∣ kernel column ∣ ≤ columnBound

open FixedOutputFourierFibre public

fixedOutputMatrix :
  ∀ {Column : Set} →
  FixedOutputFourierFibre Column → Rect.RectMatrix ⊤ Column
fixedOutputMatrix fibre tt column = kernel fibre column

fixedOutputVectorNormSq :
  ∀ {Column : Set} →
  FixedOutputFourierFibre Column →
  Rect.Vector Column → ℚ
fixedOutputVectorNormSq fibre vector =
  Rect.rectVectorNormSq (columns fibre) vector

fixedOutputApply :
  ∀ {Column : Set} →
  (fibre : FixedOutputFourierFibre Column) →
  Rect.Vector Column → ℚ
fixedOutputApply fibre vector =
  Rect.rectApply (columns fibre) (fixedOutputMatrix fibre) vector tt

fixedOutputRowMassExact :
  ∀ {Column : Set}
    (fibre : FixedOutputFourierFibre Column) →
  Rect.rectAbsoluteRowMass
    (columns fibre) (fixedOutputMatrix fibre) tt
  ≡ Sums.sumRational (columns fibre) (λ column → ∣ kernel fibre column ∣)
fixedOutputRowMassExact fibre = refl

fixedOutputColumnMassExact :
  ∀ {Column : Set}
    (fibre : FixedOutputFourierFibre Column)
    (column : Column) →
  Rect.rectAbsoluteColumnMass
    (tt ∷ []) (fixedOutputMatrix fibre) column
  ≡ ∣ kernel fibre column ∣
fixedOutputColumnMassExact fibre column =
  ℚP.+-identityʳ ∣ kernel fibre column ∣

fixedOutputRowBoundForSchur :
  ∀ {Column : Set}
    (fibre : FixedOutputFourierFibre Column) →
  Rect.rectAbsoluteRowMass
    (columns fibre) (fixedOutputMatrix fibre) tt
  ≤ rowBound fibre
fixedOutputRowBoundForSchur fibre =
  subst
    (λ left → left ≤ rowBound fibre)
    (sym (fixedOutputRowMassExact fibre))
    (wholeAbsoluteFibreMassBound fibre)

fixedOutputColumnBoundForSchur :
  ∀ {Column : Set}
    (fibre : FixedOutputFourierFibre Column)
    (column : Column) →
  Rect.rectAbsoluteColumnMass
    (tt ∷ []) (fixedOutputMatrix fibre) column
  ≤ columnBound fibre
fixedOutputColumnBoundForSchur fibre column =
  subst
    (λ left → left ≤ columnBound fibre)
    (sym (fixedOutputColumnMassExact fibre column))
    (everyColumnMassBound fibre column)

fixedOutputFibreSchurSquared :
  ∀ {Column : Set}
    (fibre : FixedOutputFourierFibre Column)
    (vector : Rect.Vector Column) →
  L2.square (fixedOutputApply fibre vector)
  ≤ (rowBound fibre * columnBound fibre)
      * fixedOutputVectorNormSq fibre vector
fixedOutputFibreSchurSquared fibre vector =
  let
    schur =
      Rect.finiteRectangularSchurSquared
        (tt ∷ [])
        (columns fibre)
        (fixedOutputMatrix fibre)
        vector
        (rowBound fibre)
        (columnBound fibre)
        (rowBoundNonnegative fibre)
        (columnBoundNonnegative fibre)
        (λ { tt → fixedOutputRowBoundForSchur fibre })
        (fixedOutputColumnBoundForSchur fibre)

    leftMeaning :
      Rect.rectVectorNormSq (tt ∷ [])
        (Rect.rectApply (columns fibre) (fixedOutputMatrix fibre) vector)
      ≡ L2.square (fixedOutputApply fibre vector)
    leftMeaning = ℚP.+-identityʳ (L2.square (fixedOutputApply fibre vector))
  in
  subst
    (λ left →
      left
      ≤ (rowBound fibre * columnBound fibre)
          * fixedOutputVectorNormSq fibre vector)
    leftMeaning
    schur

record UnitColumnFixedOutputFibre (Column : Set) : Set₁ where
  field
    fibre : FixedOutputFourierFibre Column
    columnBoundIsOne : columnBound fibre ≡ 1ℚ

open UnitColumnFixedOutputFibre public

fixedOutputFibreSchurAtRowMass :
  ∀ {Column : Set}
    (unit : UnitColumnFixedOutputFibre Column)
    (vector : Rect.Vector Column) →
  L2.square (fixedOutputApply (fibre unit) vector)
  ≤ rowBound (fibre unit) * fixedOutputVectorNormSq (fibre unit) vector
fixedOutputFibreSchurAtRowMass unit vector =
  let
    base = fixedOutputFibreSchurSquared (fibre unit) vector
    rhsMeaning :
      (rowBound (fibre unit) * columnBound (fibre unit))
        * fixedOutputVectorNormSq (fibre unit) vector
      ≡ rowBound (fibre unit) * fixedOutputVectorNormSq (fibre unit) vector
    rhsMeaning
      rewrite columnBoundIsOne unit =
      solve
        ( rowBound (fibre unit)
        ∷ fixedOutputVectorNormSq (fibre unit) vector
        ∷ [])
  in
  subst
    (λ right →
      L2.square (fixedOutputApply (fibre unit) vector) ≤ right)
    rhsMeaning
    base

comSameOutputCollisionsReducedToWholeFibreMass : Bool
comSameOutputCollisionsReducedToWholeFibreMass = true

noTriadCardinalityFactorAfterWholeFibreMassBound : Bool
noTriadCardinalityFactorAfterWholeFibreMassBound = true

physicalOddPQFibreMassBoundsConstructed : Bool
physicalOddPQFibreMassBoundsConstructed = false

comSameOutputCollisionsReducedToWholeFibreMassIsTrue :
  comSameOutputCollisionsReducedToWholeFibreMass ≡ true
comSameOutputCollisionsReducedToWholeFibreMassIsTrue = refl

noTriadCardinalityFactorAfterWholeFibreMassBoundIsTrue :
  noTriadCardinalityFactorAfterWholeFibreMassBound ≡ true
noTriadCardinalityFactorAfterWholeFibreMassBoundIsTrue = refl
