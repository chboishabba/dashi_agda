module DASHI.Physics.YangMills.BalabanP33CoarseFineSchurCouplingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Volker Bach, Thomas Chen, Jürg Fröhlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- SCOPE SOURCE
--
-- Toby S. Cubitt, David Pérez-García and Michael M. Wolf,
-- "Undecidability of the Spectral Gap", Forum of Mathematics, Pi 10
-- (2022), e14. DOI: 10.1017/fmp.2021.15.
-- Short version: Nature 528 (2015), 207--211.
-- DOI: 10.1038/nature16059.
--
-- The undecidability theorem is not imported as an Agda proof.  It explains
-- why the physical infinite-volume step cannot be a generic finite-operator
-- promotion.  The theorem below is deliberately only the exact finite
-- square-root-free coupling estimate needed inside a structure-specific RG
-- step.
--
-- DASHI CONTRIBUTION
--
-- Isolate the coarse--fine coupling B as its own quantitative producer.
-- From absolute row and column bounds
--
--   row(B) <= r_B,  column(B) <= c_B,
--
-- the existing finite Schur test gives
--
--   ||B v||^2 <= beta ||v||^2,  beta = r_B c_B.
--
-- If the fluctuation inverse has coefficient
--
--   ||C^-1 v||^2 <= gamma ||v||^2,
--   gamma = r_C c_C,
--
-- then the Feshbach feedback obeys the exact square-root-free estimate
--
--   ||B C^-1 B^T v||^2 <= beta^2 gamma ||v||^2.
--
-- This prevents ||B|| control from being silently folded into a generic
-- remainder.  A physical RG step must instantiate the actual B and C^-1
-- matrices and prove their row/column bounds uniformly in scale.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur

transpose :
  ∀ {Index : Set} → Schur.Matrix Index → Schur.Matrix Index
transpose matrix row column = matrix column row

transposeRowMassExact :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Schur.Matrix Index)
    (index : Index) →
  Schur.absoluteRowMass indices (transpose matrix) index
  ≡ Schur.absoluteColumnMass indices matrix index
transposeRowMassExact indices matrix index = refl

transposeColumnMassExact :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Schur.Matrix Index)
    (index : Index) →
  Schur.absoluteColumnMass indices (transpose matrix) index
  ≡ Schur.absoluteRowMass indices matrix index
transposeColumnMassExact indices matrix index = refl

scaleMonotone :
  ∀ scale {left right} →
  0ℚ ≤ scale →
  left ≤ right →
  scale * left ≤ scale * right
scaleMonotone scale scaleNonnegative leftBelowRight =
  let
    instance
      scaleNN : NonNegative scale
      scaleNN = ℚ.nonNegative scaleNonnegative
  in
  ℚP.*-monoˡ-≤-nonNeg scale leftBelowRight

transposeSchurSquared :
  ∀ {Index : Set}
    (indices : List Index)
    (matrix : Schur.Matrix Index)
    (vector : Schur.Vector Index)
    (rowBound columnBound : ℚ) →
  0ℚ ≤ rowBound →
  0ℚ ≤ columnBound →
  (∀ row → Schur.absoluteRowMass indices matrix row ≤ rowBound) →
  (∀ column →
    Schur.absoluteColumnMass indices matrix column ≤ columnBound) →
  Schur.vectorNormSq indices
    (Schur.matrixApply indices (transpose matrix) vector)
  ≤ (rowBound * columnBound)
      * Schur.vectorNormSq indices vector
transposeSchurSquared
    indices matrix vector rowBound columnBound
    rowNonnegative columnNonnegative
    rowsBounded columnsBounded =
  let
    raw :
      Schur.vectorNormSq indices
        (Schur.matrixApply indices (transpose matrix) vector)
      ≤ (columnBound * rowBound)
          * Schur.vectorNormSq indices vector
    raw =
      Schur.finiteSchurSquared
        indices (transpose matrix) vector
        columnBound rowBound
        columnNonnegative rowNonnegative
        (λ row →
          subst
            (λ selected → selected ≤ columnBound)
            (sym (transposeRowMassExact indices matrix row))
            (columnsBounded row))
        (λ column →
          subst
            (λ selected → selected ≤ rowBound)
            (sym (transposeColumnMassExact indices matrix column))
            (rowsBounded column))
  in
  subst
    (λ upper →
      Schur.vectorNormSq indices
        (Schur.matrixApply indices (transpose matrix) vector)
      ≤ upper)
    (ℚRing.solve-∀
      rowBound columnBound
      (Schur.vectorNormSq indices vector))
    raw

couplingSquaredCoefficient : ℚ → ℚ → ℚ
couplingSquaredCoefficient rowBound columnBound =
  rowBound * columnBound

schurFeedbackSquaredCoefficient :
  ℚ → ℚ → ℚ → ℚ → ℚ
schurFeedbackSquaredCoefficient
    couplingRow couplingColumn inverseRow inverseColumn =
  couplingSquaredCoefficient couplingRow couplingColumn
  * (inverseRow * inverseColumn)
  * couplingSquaredCoefficient couplingRow couplingColumn

schurFeedbackApply :
  ∀ {Index : Set} →
  List Index →
  Schur.Matrix Index →
  Schur.Matrix Index →
  Schur.Vector Index →
  Schur.Vector Index
schurFeedbackApply indices coupling fluctuationInverse vector =
  Schur.matrixApply indices coupling
    (Schur.matrixApply indices fluctuationInverse
      (Schur.matrixApply indices (transpose coupling) vector))

coarseFineSchurFeedbackSquared :
  ∀ {Index : Set}
    (indices : List Index)
    (coupling fluctuationInverse : Schur.Matrix Index)
    (vector : Schur.Vector Index)
    (couplingRow couplingColumn inverseRow inverseColumn : ℚ) →
  0ℚ ≤ couplingRow →
  0ℚ ≤ couplingColumn →
  0ℚ ≤ inverseRow →
  0ℚ ≤ inverseColumn →
  (∀ row →
    Schur.absoluteRowMass indices coupling row ≤ couplingRow) →
  (∀ column →
    Schur.absoluteColumnMass indices coupling column ≤ couplingColumn) →
  (∀ row →
    Schur.absoluteRowMass indices fluctuationInverse row ≤ inverseRow) →
  (∀ column →
    Schur.absoluteColumnMass indices fluctuationInverse column ≤ inverseColumn) →
  Schur.vectorNormSq indices
    (schurFeedbackApply indices coupling fluctuationInverse vector)
  ≤ schurFeedbackSquaredCoefficient
      couplingRow couplingColumn inverseRow inverseColumn
      * Schur.vectorNormSq indices vector
coarseFineSchurFeedbackSquared
    indices coupling fluctuationInverse vector
    couplingRow couplingColumn inverseRow inverseColumn
    couplingRowNonnegative couplingColumnNonnegative
    inverseRowNonnegative inverseColumnNonnegative
    couplingRows couplingColumns inverseRows inverseColumns =
  let
    beta = couplingSquaredCoefficient couplingRow couplingColumn
    gamma = inverseRow * inverseColumn

    betaNonnegative : 0ℚ ≤ beta
    betaNonnegative =
      Schur.productNonnegative
        couplingRow couplingColumn
        couplingRowNonnegative couplingColumnNonnegative

    gammaNonnegative : 0ℚ ≤ gamma
    gammaNonnegative =
      Schur.productNonnegative
        inverseRow inverseColumn
        inverseRowNonnegative inverseColumnNonnegative

    transposed = Schur.matrixApply indices (transpose coupling) vector
    propagated =
      Schur.matrixApply indices fluctuationInverse transposed

    transposedBound :
      Schur.vectorNormSq indices transposed
      ≤ beta * Schur.vectorNormSq indices vector
    transposedBound =
      transposeSchurSquared
        indices coupling vector couplingRow couplingColumn
        couplingRowNonnegative couplingColumnNonnegative
        couplingRows couplingColumns

    inverseRaw :
      Schur.vectorNormSq indices propagated
      ≤ gamma * Schur.vectorNormSq indices transposed
    inverseRaw =
      Schur.finiteSchurSquared
        indices fluctuationInverse transposed inverseRow inverseColumn
        inverseRowNonnegative inverseColumnNonnegative
        inverseRows inverseColumns

    inverseScaled :
      gamma * Schur.vectorNormSq indices transposed
      ≤ gamma * (beta * Schur.vectorNormSq indices vector)
    inverseScaled =
      scaleMonotone gamma gammaNonnegative transposedBound

    propagatedBound :
      Schur.vectorNormSq indices propagated
      ≤ gamma * (beta * Schur.vectorNormSq indices vector)
    propagatedBound = ℚP.≤-trans inverseRaw inverseScaled

    outerRaw :
      Schur.vectorNormSq indices
        (Schur.matrixApply indices coupling propagated)
      ≤ beta * Schur.vectorNormSq indices propagated
    outerRaw =
      Schur.finiteSchurSquared
        indices coupling propagated couplingRow couplingColumn
        couplingRowNonnegative couplingColumnNonnegative
        couplingRows couplingColumns

    outerScaled :
      beta * Schur.vectorNormSq indices propagated
      ≤ beta * (gamma * (beta * Schur.vectorNormSq indices vector))
    outerScaled =
      scaleMonotone beta betaNonnegative propagatedBound

    combined :
      Schur.vectorNormSq indices
        (schurFeedbackApply indices coupling fluctuationInverse vector)
      ≤ beta * (gamma * (beta * Schur.vectorNormSq indices vector))
    combined = ℚP.≤-trans outerRaw outerScaled
  in
  subst
    (λ upper →
      Schur.vectorNormSq indices
        (schurFeedbackApply indices coupling fluctuationInverse vector)
      ≤ upper)
    (ℚRing.solve-∀
      beta gamma (Schur.vectorNormSq indices vector))
    combined

coarseFineCouplingSchurLevel : ProofLevel
coarseFineCouplingSchurLevel = machineChecked

physicalCoarseFineCouplingBoundsLevel : ProofLevel
physicalCoarseFineCouplingBoundsLevel = conditional

spectralGapUndecidabilityScopeSourceLevel : ProofLevel
spectralGapUndecidabilityScopeSourceLevel = standardImported
