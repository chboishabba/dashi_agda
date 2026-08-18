module DASHI.Physics.YangMills.BalabanReducedGhostSignedMatrixLogTailExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- DASHI CONTRIBUTION
--
-- Replace the unsigned majorant tail by the actual alternating matrix-log
-- recursion.  Starting at degree five,
--
--   T_N(R;c) = c_0 R^5 - R T_{N-1}(R;shift c),
--
-- so expansion gives
--
--   c_0 R^5 - c_1 R^6 + c_2 R^7 - ... .
--
-- The sign changes cost nothing in row mass because rowMass(-A)=rowMass(A).
-- Hence the already-proved q=1/5 geometric majorant and 1/2500 cap apply to
-- the literal signed tail itself, not merely to an unrelated positive series.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Tail

matrixNegate : ∀ {Index : Set} → Matrix.Matrix Index → Matrix.Matrix Index
matrixNegate matrix row column = - matrix row column

matrixSubtract : ∀ {Index : Set} →
  Matrix.Matrix Index → Matrix.Matrix Index → Matrix.Matrix Index
matrixSubtract left right row column = left row column - right row column

matrixNegateRowMassExact :
  ∀ {Index : Set} (indices : List Index)
    (matrix : Matrix.Matrix Index) row →
  Neumann.rowMass indices (matrixNegate matrix) row
  ≡ Neumann.rowMass indices matrix row
matrixNegateRowMassExact indices matrix row =
  Sums.sumRationalCong indices _ _
    (λ column → ℚP.∣-p∣≡∣p∣ (matrix row column))

matrixSubtractRowMassBound :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) leftBound rightBound →
  Neumann.UniformRowBound indices left leftBound →
  Neumann.UniformRowBound indices right rightBound →
  Neumann.UniformRowBound indices (matrixSubtract left right)
    (leftBound + rightBound)
matrixSubtractRowMassBound indices left right leftBound rightBound
    leftRows rightRows row =
  let
    triangle = Schur.sumPointwiseBelow indices
      (λ column → ∣ left row column - right row column ∣)
      (λ column → ∣ left row column ∣ + ∣ right row column ∣)
      (λ column →
        let
          subtractAsAdd :
            left row column - right row column
            ≡ left row column + (- right row column)
          subtractAsAdd = ℚRing.solve-∀
            (left row column) (right row column)
          raw = ℚP.∣p+q∣≤∣p∣+∣q∣
            (left row column) (- right row column)
        in
        subst
          (λ lower → lower ≤ ∣ left row column ∣ + ∣ right row column ∣)
          (cong ∣_∣ subtractAsAdd)
          (subst
            (λ upper →
              ∣ left row column + (- right row column) ∣
              ≤ ∣ left row column ∣ + upper)
            (ℚP.∣-p∣≡∣p∣ (right row column)) raw))
    split = Fubini.sumRationalAdd indices
      (λ column → ∣ left row column ∣)
      (λ column → ∣ right row column ∣)
  in
  ℚP.≤-trans
    (subst
      (λ upper →
        Neumann.rowMass indices (matrixSubtract left right) row ≤ upper)
      split triangle)
    (ℚP.+-mono-≤ (leftRows row) (rightRows row))

------------------------------------------------------------------------
-- Actual signed degree-five-and-higher finite tail.
------------------------------------------------------------------------

signedFifthTail :
  ∀ {Index : Set} →
  List Index → Matrix.Matrix Index → Tail.LogTailCoefficients →
  Nat → Matrix.Matrix Index
signedFifthTail indices matrix coefficients zero =
  Neumann.scaleMatrix
    (Tail.coefficient coefficients zero) (Tail.fifthPower indices matrix)
signedFifthTail indices matrix coefficients (suc exponent) =
  matrixSubtract
    (Neumann.scaleMatrix
      (Tail.coefficient coefficients zero) (Tail.fifthPower indices matrix))
    (Matrix.matrixProduct indices matrix
      (signedFifthTail indices matrix (Tail.shiftCoefficients coefficients) exponent))

signedFifthTailRowBound :
  ∀ {Index : Set} (indices : List Index) (matrix : Matrix.Matrix Index)
    (coefficients : Tail.LogTailCoefficients) exponent →
  Neumann.UniformRowBound indices matrix Tail.oneFifth →
  Neumann.UniformRowBound indices
    (signedFifthTail indices matrix coefficients exponent)
    (Tail.geometricMajorant exponent)
signedFifthTailRowBound indices matrix coefficients zero matrixRows =
  Neumann.unitCoefficientPreservesRowBound
    indices (Tail.coefficient coefficients zero)
    (Tail.fifthPower indices matrix) Tail.oneFifthFifth
    (Tail.coefficientNonnegative coefficients zero)
    (Tail.coefficientBelowOne coefficients zero)
    Tail.oneFifthFifthNonnegative
    (Tail.fifthPowerRowBound indices matrix matrixRows)
signedFifthTailRowBound indices matrix coefficients (suc exponent) matrixRows =
  let
    first = Neumann.scaleMatrix
      (Tail.coefficient coefficients zero) (Tail.fifthPower indices matrix)
    rest = signedFifthTail
      indices matrix (Tail.shiftCoefficients coefficients) exponent

    firstRows :
      Neumann.UniformRowBound indices first Tail.oneFifthFifth
    firstRows = Neumann.unitCoefficientPreservesRowBound
      indices (Tail.coefficient coefficients zero)
      (Tail.fifthPower indices matrix) Tail.oneFifthFifth
      (Tail.coefficientNonnegative coefficients zero)
      (Tail.coefficientBelowOne coefficients zero)
      Tail.oneFifthFifthNonnegative
      (Tail.fifthPowerRowBound indices matrix matrixRows)

    restRows :
      Neumann.UniformRowBound indices rest (Tail.geometricMajorant exponent)
    restRows = signedFifthTailRowBound
      indices matrix (Tail.shiftCoefficients coefficients) exponent matrixRows

    productRows :
      Neumann.UniformRowBound indices
        (Matrix.matrixProduct indices matrix rest)
        (Tail.oneFifth * Tail.geometricMajorant exponent)
    productRows = Neumann.productRowMassBound
      indices matrix rest Tail.oneFifth (Tail.geometricMajorant exponent)
      (Tail.geometricMajorantNonnegative exponent)
      matrixRows restRows

    combined = matrixSubtractRowMassBound
      indices first (Matrix.matrixProduct indices matrix rest)
      Tail.oneFifthFifth (Tail.oneFifth * Tail.geometricMajorant exponent)
      firstRows productRows

    boundExact :
      Tail.oneFifthFifth + Tail.oneFifth * Tail.geometricMajorant exponent
      ≡ Tail.geometricMajorant (suc exponent)
    boundExact = ℚRing.solve-∀
      (Geometric.finiteGeometricSum Tail.oneFifth exponent)
      where
      import DASHI.Physics.Closure.NSTriadKNLuoFiniteGeometricResidualTailExact as Geometric
  in
  λ row → subst
    (λ bound →
      Neumann.rowMass indices
        (signedFifthTail indices matrix coefficients (suc exponent)) row ≤ bound)
    boundExact (combined row)

signedFifthTailUniformCap :
  ∀ {Index : Set} (indices : List Index) (matrix : Matrix.Matrix Index)
    (coefficients : Tail.LogTailCoefficients) exponent →
  Neumann.UniformRowBound indices matrix Tail.oneFifth →
  Neumann.UniformRowBound indices
    (signedFifthTail indices matrix coefficients exponent)
    Tail.fifthTailCap
signedFifthTailUniformCap indices matrix coefficients exponent matrixRows row =
  ℚP.≤-trans
    (signedFifthTailRowBound
      indices matrix coefficients exponent matrixRows row)
    (Tail.geometricMajorantBelowFifthTailCap exponent)

reducedGhostSignedMatrixLogTailLevel : ProofLevel
reducedGhostSignedMatrixLogTailLevel = machineChecked
