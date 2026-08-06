module DASHI.Physics.YangMills.BalabanP33KernelDecayToSchurExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Lin Lin and Jianfeng Lu,
-- "Decay Estimates of Discretized Green's Functions for Schrödinger Type
-- Operators", Science China Mathematics 59 (2016), 1561--1578.
-- DOI: 10.1007/s11425-016-0311-4.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Close the finite algebra between an entrywise locality estimate and the
-- row/column bounds consumed by the Stage-II Schur/Feshbach theorem.
-- If
--
--   |K(x,y)| <= amplitude * weight(x,y),
--
-- and the literal finite weight has row mass at most R and column mass at most
-- C, then
--
--   row(K) <= amplitude*R,
--   column(K) <= amplitude*C,
--   ||K v||^2 <= amplitude^2 R C ||v||^2.
--
-- This is the exact bridge needed after a scale-uniform Combes--Thomas estimate
-- for C_j^-1 and after a finite-stencil estimate for B_j.  It does not assert
-- either physical estimate; it removes the remaining summation and coefficient
-- bookkeeping once those pointwise bounds are proved.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur

kernelMajorantRowMass :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix weight : Schur.Matrix Index)
    (amplitude rowWeightBound : ℚ) →
  0ℚ ≤ amplitude →
  (∀ row column →
    ∣ matrix row column ∣ ≤ amplitude * weight row column) →
  (∀ row →
    Sums.sumRational indices (weight row) ≤ rowWeightBound) →
  ∀ row →
  Schur.absoluteRowMass indices matrix row
  ≤ amplitude * rowWeightBound
kernelMajorantRowMass
    indices matrix weight amplitude rowWeightBound
    amplitudeNonnegative entryBound weightRows row =
  let
    pointwiseSum :
      Schur.absoluteRowMass indices matrix row
      ≤ Sums.sumRational indices
          (λ column → amplitude * weight row column)
    pointwiseSum =
      Schur.sumPointwiseBelow
        indices
        (λ column → ∣ matrix row column ∣)
        (λ column → amplitude * weight row column)
        (entryBound row)

    scaledWeightExact :
      Sums.sumRational indices
        (λ column → amplitude * weight row column)
      ≡ amplitude * Sums.sumRational indices (weight row)
    scaledWeightExact =
      Sums.sumRationalScale amplitude indices (weight row)

    scaledWeightBound :
      amplitude * Sums.sumRational indices (weight row)
      ≤ amplitude * rowWeightBound
    scaledWeightBound =
      let
        instance
          amplitudeNN : NonNegative amplitude
          amplitudeNN = ℚ.nonNegative amplitudeNonnegative
      in
      ℚP.*-monoˡ-≤-nonNeg amplitude (weightRows row)
  in
  ℚP.≤-trans
    (subst
      (λ upper →
        Schur.absoluteRowMass indices matrix row ≤ upper)
      scaledWeightExact
      pointwiseSum)
    scaledWeightBound

kernelMajorantColumnMass :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix weight : Schur.Matrix Index)
    (amplitude columnWeightBound : ℚ) →
  0ℚ ≤ amplitude →
  (∀ row column →
    ∣ matrix row column ∣ ≤ amplitude * weight row column) →
  (∀ column →
    Sums.sumRational indices (λ row → weight row column)
    ≤ columnWeightBound) →
  ∀ column →
  Schur.absoluteColumnMass indices matrix column
  ≤ amplitude * columnWeightBound
kernelMajorantColumnMass
    indices matrix weight amplitude columnWeightBound
    amplitudeNonnegative entryBound weightColumns column =
  let
    pointwiseSum :
      Schur.absoluteColumnMass indices matrix column
      ≤ Sums.sumRational indices
          (λ row → amplitude * weight row column)
    pointwiseSum =
      Schur.sumPointwiseBelow
        indices
        (λ row → ∣ matrix row column ∣)
        (λ row → amplitude * weight row column)
        (λ row → entryBound row column)

    scaledWeightExact :
      Sums.sumRational indices
        (λ row → amplitude * weight row column)
      ≡ amplitude
        * Sums.sumRational indices (λ row → weight row column)
    scaledWeightExact =
      Sums.sumRationalScale amplitude indices
        (λ row → weight row column)

    scaledWeightBound :
      amplitude
        * Sums.sumRational indices (λ row → weight row column)
      ≤ amplitude * columnWeightBound
    scaledWeightBound =
      let
        instance
          amplitudeNN : NonNegative amplitude
          amplitudeNN = ℚ.nonNegative amplitudeNonnegative
      in
      ℚP.*-monoˡ-≤-nonNeg amplitude (weightColumns column)
  in
  ℚP.≤-trans
    (subst
      (λ upper →
        Schur.absoluteColumnMass indices matrix column ≤ upper)
      scaledWeightExact
      pointwiseSum)
    scaledWeightBound

kernelMajorantSchurSquared :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix weight : Schur.Matrix Index)
    (vector : Schur.Vector Index)
    (amplitude rowWeightBound columnWeightBound : ℚ) →
  0ℚ ≤ amplitude →
  0ℚ ≤ rowWeightBound →
  0ℚ ≤ columnWeightBound →
  (∀ row column →
    ∣ matrix row column ∣ ≤ amplitude * weight row column) →
  (∀ row →
    Sums.sumRational indices (weight row) ≤ rowWeightBound) →
  (∀ column →
    Sums.sumRational indices (λ row → weight row column)
    ≤ columnWeightBound) →
  Schur.vectorNormSq indices
    (Schur.matrixApply indices matrix vector)
  ≤ (amplitude * amplitude * rowWeightBound * columnWeightBound)
      * Schur.vectorNormSq indices vector
kernelMajorantSchurSquared
    indices matrix weight vector
    amplitude rowWeightBound columnWeightBound
    amplitudeNonnegative rowWeightNonnegative columnWeightNonnegative
    entryBound weightRows weightColumns =
  let
    rowBound = amplitude * rowWeightBound
    columnBound = amplitude * columnWeightBound

    rowBoundNonnegative : 0ℚ ≤ rowBound
    rowBoundNonnegative =
      Schur.productNonnegative
        amplitude rowWeightBound
        amplitudeNonnegative rowWeightNonnegative

    columnBoundNonnegative : 0ℚ ≤ columnBound
    columnBoundNonnegative =
      Schur.productNonnegative
        amplitude columnWeightBound
        amplitudeNonnegative columnWeightNonnegative

    raw :
      Schur.vectorNormSq indices
        (Schur.matrixApply indices matrix vector)
      ≤ (rowBound * columnBound)
          * Schur.vectorNormSq indices vector
    raw =
      Schur.finiteSchurSquared
        indices matrix vector rowBound columnBound
        rowBoundNonnegative columnBoundNonnegative
        (kernelMajorantRowMass
          indices matrix weight amplitude rowWeightBound
          amplitudeNonnegative entryBound weightRows)
        (kernelMajorantColumnMass
          indices matrix weight amplitude columnWeightBound
          amplitudeNonnegative entryBound weightColumns)
  in
  subst
    (λ coefficient →
      Schur.vectorNormSq indices
        (Schur.matrixApply indices matrix vector)
      ≤ coefficient * Schur.vectorNormSq indices vector)
    (ℚRing.solve-∀ amplitude rowWeightBound columnWeightBound)
    raw

kernelDecayToRowMassLevel : ProofLevel
kernelDecayToRowMassLevel = machineChecked

kernelDecayToColumnMassLevel : ProofLevel
kernelDecayToColumnMassLevel = machineChecked

kernelDecayToSchurLevel : ProofLevel
kernelDecayToSchurLevel = machineChecked

physicalUniformFluctuationInverseDecayProducerLevel : ProofLevel
physicalUniformFluctuationInverseDecayProducerLevel = conditional

physicalUniformCouplingStencilProducerLevel : ProofLevel
physicalUniformCouplingStencilProducerLevel = conditional
