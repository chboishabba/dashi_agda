module DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact where

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
-- DASHI CONTRIBUTION
--
-- The literal anchored reduced Faddeev--Popov relative operator now satisfies
-- the physical row-mass contraction q < 1/5.  This file closes the generic
-- degree-five-and-higher matrix-log tail bookkeeping on the same finite matrix
-- carrier.
--
-- For any coefficients c_n with 0 <= c_n <= 1 (hence for |1/(n+5)|), define
-- the finite majorised tail recursively from R^5.  Row-mass
-- submultiplicativity gives
--
--   rowMass(tail_N)
--     <= (1/5)^5 sum_{j=0}^N (1/5)^j
--     <= 1/2500.
--
-- The scalar cap reuses the repository's exact finite geometric identity.  No
-- determinant, continuum limit or physical Taylor remainder is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGeometricResidualTailExact as Geometric
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

oneFifth oneFifthFifth fifthTailCap fourFifths : ℚ
oneFifth = + 1 / 5
oneFifthFifth = + 1 / 3125
fifthTailCap = + 1 / 2500
fourFifths = + 4 / 5

oneFifthNonnegative : 0ℚ ≤ oneFifth
oneFifthNonnegative = ℚP.nonNegative⁻¹ oneFifth

oneFifthFifthNonnegative : 0ℚ ≤ oneFifthFifth
oneFifthFifthNonnegative = ℚP.nonNegative⁻¹ oneFifthFifth

fifthTailCapNonnegative : 0ℚ ≤ fifthTailCap
fifthTailCapNonnegative = ℚP.nonNegative⁻¹ fifthTailCap

oneFifthPowerFiveExact :
  Neumann.rationalPower oneFifth (suc (suc (suc (suc (suc zero)))))
  ≡ oneFifthFifth
oneFifthPowerFiveExact = ℚRing.solve []

matrixAdd : ∀ {Index : Set} →
  Matrix.Matrix Index → Matrix.Matrix Index → Matrix.Matrix Index
matrixAdd left right row column = left row column + right row column

matrixAddRowMassBound :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) leftBound rightBound →
  Neumann.UniformRowBound indices left leftBound →
  Neumann.UniformRowBound indices right rightBound →
  Neumann.UniformRowBound indices (matrixAdd left right)
    (leftBound + rightBound)
matrixAddRowMassBound indices left right leftBound rightBound
    leftRows rightRows row =
  let
    pointwise = Schur.sumPointwiseBelow indices
      (λ column → ∣ left row column + right row column ∣)
      (λ column → ∣ left row column ∣ + ∣ right row column ∣)
      (λ column → ℚP.∣p+q∣≤∣p∣+∣q∣
        (left row column) (right row column))

    split = Fubini.sumRationalAdd indices
      (λ column → ∣ left row column ∣)
      (λ column → ∣ right row column ∣)
  in
  ℚP.≤-trans
    (subst
      (λ upper → Neumann.rowMass indices (matrixAdd left right) row ≤ upper)
      split pointwise)
    (ℚP.+-mono-≤ (leftRows row) (rightRows row))

fifthPower : ∀ {Index : Set} →
  List Index → Matrix.Matrix Index → Matrix.Matrix Index
fifthPower indices matrix =
  Neumann.positiveMatrixPower indices matrix (suc (suc (suc (suc zero))))

fifthPowerRowBound :
  ∀ {Index : Set} (indices : List Index) (matrix : Matrix.Matrix Index) →
  Neumann.UniformRowBound indices matrix oneFifth →
  Neumann.UniformRowBound indices (fifthPower indices matrix) oneFifthFifth
fifthPowerRowBound indices matrix matrixRows row =
  subst
    (λ bound → Neumann.rowMass indices (fifthPower indices matrix) row ≤ bound)
    oneFifthPowerFiveExact
    (Neumann.positivePowerRowBound
      indices matrix oneFifth (suc (suc (suc (suc zero))))
      oneFifthNonnegative matrixRows row)

finiteGeometricNonnegative : ∀ exponent →
  0ℚ ≤ Geometric.finiteGeometricSum oneFifth exponent
finiteGeometricNonnegative zero = ℚP.nonNegative⁻¹ 1ℚ
finiteGeometricNonnegative (suc exponent) =
  let
    tail = Geometric.finiteGeometricSum oneFifth exponent
    instance
      ratioNN : NonNegative oneFifth
      ratioNN = ℚ.nonNegative oneFifthNonnegative
      tailNN : NonNegative tail
      tailNN = ℚ.nonNegative (finiteGeometricNonnegative exponent)
      productNN : NonNegative (oneFifth * tail)
      productNN = ℚP.nonNeg*nonNeg⇒nonNeg oneFifth tail
      sumNN : NonNegative (1ℚ + oneFifth * tail)
      sumNN = ℚP.nonNeg+nonNeg⇒nonNeg 1ℚ (oneFifth * tail)
  in
  ℚP.nonNegative⁻¹ (1ℚ + oneFifth * tail)

geometricMajorant : Nat → ℚ
geometricMajorant exponent =
  oneFifthFifth * Geometric.finiteGeometricSum oneFifth exponent

geometricMajorantNonnegative : ∀ exponent →
  0ℚ ≤ geometricMajorant exponent
geometricMajorantNonnegative exponent =
  let
    sum = Geometric.finiteGeometricSum oneFifth exponent
    instance
      fifthNN : NonNegative oneFifthFifth
      fifthNN = ℚ.nonNegative oneFifthFifthNonnegative
      sumNN : NonNegative sum
      sumNN = ℚ.nonNegative (finiteGeometricNonnegative exponent)
  in
  ℚP.nonNegative⁻¹ (oneFifthFifth * sum)

record LogTailCoefficients : Set₁ where
  field
    coefficient : Nat → ℚ
    coefficientNonnegative : ∀ exponent → 0ℚ ≤ coefficient exponent
    coefficientBelowOne : ∀ exponent → coefficient exponent ≤ 1ℚ
open LogTailCoefficients public

shiftCoefficients : LogTailCoefficients → LogTailCoefficients
shiftCoefficients coefficients = record
  { coefficient = λ exponent → coefficient coefficients (suc exponent)
  ; coefficientNonnegative = λ exponent →
      coefficientNonnegative coefficients (suc exponent)
  ; coefficientBelowOne = λ exponent →
      coefficientBelowOne coefficients (suc exponent)
  }

finiteFifthTail :
  ∀ {Index : Set} →
  List Index → Matrix.Matrix Index → LogTailCoefficients → Nat → Matrix.Matrix Index
finiteFifthTail indices matrix coefficients zero =
  Neumann.scaleMatrix (coefficient coefficients zero) (fifthPower indices matrix)
finiteFifthTail indices matrix coefficients (suc exponent) =
  matrixAdd
    (Neumann.scaleMatrix (coefficient coefficients zero) (fifthPower indices matrix))
    (Matrix.matrixProduct indices matrix
      (finiteFifthTail indices matrix (shiftCoefficients coefficients) exponent))

finiteFifthTailRowBound :
  ∀ {Index : Set} (indices : List Index) (matrix : Matrix.Matrix Index)
    (coefficients : LogTailCoefficients) exponent →
  Neumann.UniformRowBound indices matrix oneFifth →
  Neumann.UniformRowBound indices
    (finiteFifthTail indices matrix coefficients exponent)
    (geometricMajorant exponent)
finiteFifthTailRowBound indices matrix coefficients zero matrixRows =
  Neumann.unitCoefficientPreservesRowBound
    indices (coefficient coefficients zero)
    (fifthPower indices matrix) oneFifthFifth
    (coefficientNonnegative coefficients zero)
    (coefficientBelowOne coefficients zero)
    oneFifthFifthNonnegative
    (fifthPowerRowBound indices matrix matrixRows)
finiteFifthTailRowBound indices matrix coefficients (suc exponent) matrixRows =
  let
    first = Neumann.scaleMatrix
      (coefficient coefficients zero) (fifthPower indices matrix)
    rest = finiteFifthTail indices matrix (shiftCoefficients coefficients) exponent

    firstRows : Neumann.UniformRowBound indices first oneFifthFifth
    firstRows = Neumann.unitCoefficientPreservesRowBound
      indices (coefficient coefficients zero)
      (fifthPower indices matrix) oneFifthFifth
      (coefficientNonnegative coefficients zero)
      (coefficientBelowOne coefficients zero)
      oneFifthFifthNonnegative
      (fifthPowerRowBound indices matrix matrixRows)

    restRows : Neumann.UniformRowBound indices rest (geometricMajorant exponent)
    restRows = finiteFifthTailRowBound
      indices matrix (shiftCoefficients coefficients) exponent matrixRows

    productRows :
      Neumann.UniformRowBound indices
        (Matrix.matrixProduct indices matrix rest)
        (oneFifth * geometricMajorant exponent)
    productRows = Neumann.productRowMassBound
      indices matrix rest oneFifth (geometricMajorant exponent)
      (geometricMajorantNonnegative exponent)
      matrixRows restRows

    combined = matrixAddRowMassBound
      indices first (Matrix.matrixProduct indices matrix rest)
      oneFifthFifth (oneFifth * geometricMajorant exponent)
      firstRows productRows

    boundExact :
      oneFifthFifth + oneFifth * geometricMajorant exponent
      ≡ geometricMajorant (suc exponent)
    boundExact = ℚRing.solve-∀
      (Geometric.finiteGeometricSum oneFifth exponent)
  in
  λ row → subst
    (λ bound →
      Neumann.rowMass indices
        (finiteFifthTail indices matrix coefficients (suc exponent)) row
      ≤ bound)
    boundExact (combined row)

rationalPowerNonnegative : ∀ exponent →
  0ℚ ≤ Geometric.rationalPower oneFifth exponent
rationalPowerNonnegative zero = ℚP.nonNegative⁻¹ 1ℚ
rationalPowerNonnegative (suc exponent) =
  let
    power = Geometric.rationalPower oneFifth exponent
    instance
      ratioNN : NonNegative oneFifth
      ratioNN = ℚ.nonNegative oneFifthNonnegative
      powerNN : NonNegative power
      powerNN = ℚ.nonNegative (rationalPowerNonnegative exponent)
  in
  ℚP.nonNegative⁻¹ (oneFifth * power)

geometricMajorantBelowFifthTailCap : ∀ exponent →
  geometricMajorant exponent ≤ fifthTailCap
geometricMajorantBelowFifthTailCap exponent =
  let
    sum = Geometric.finiteGeometricSum oneFifth exponent
    power = Geometric.rationalPower oneFifth (suc exponent)

    rhsBelowOne : 1ℚ - power ≤ 1ℚ
    rhsBelowOne =
      FiniteL2.subtractNonnegativeBelow
        1ℚ power (rationalPowerNonnegative (suc exponent))

    oneMinusRatioExact : 1ℚ - oneFifth ≡ fourFifths
    oneMinusRatioExact = ℚRing.solve []

    scaledIdentity : fourFifths * sum ≡ 1ℚ - power
    scaledIdentity = trans
      (cong (λ coefficient → coefficient * sum) (sym oneMinusRatioExact))
      (Geometric.finiteGeometricIdentity oneFifth exponent)

    scaledSumBelowOne : fourFifths * sum ≤ 1ℚ
    scaledSumBelowOne = subst
      (λ left → left ≤ 1ℚ)
      (sym scaledIdentity)
      rhsBelowOne

    scaledByCap :
      fifthTailCap * (fourFifths * sum) ≤ fifthTailCap * 1ℚ
    scaledByCap =
      let
        instance capNN : NonNegative fifthTailCap
        capNN = ℚ.nonNegative fifthTailCapNonnegative
      in
      ℚP.*-monoˡ-≤-nonNeg fifthTailCap scaledSumBelowOne

    leftExact :
      fifthTailCap * (fourFifths * sum)
      ≡ oneFifthFifth * sum
    leftExact = ℚRing.solve-∀ sum

    rightExact : fifthTailCap * 1ℚ ≡ fifthTailCap
    rightExact = ℚP.*-identityʳ fifthTailCap
  in
  subst
    (λ left → left ≤ fifthTailCap)
    leftExact
    (subst
      (λ right → fifthTailCap * (fourFifths * sum) ≤ right)
      rightExact scaledByCap)

finiteFifthTailUniformCap :
  ∀ {Index : Set} (indices : List Index) (matrix : Matrix.Matrix Index)
    (coefficients : LogTailCoefficients) exponent →
  Neumann.UniformRowBound indices matrix oneFifth →
  Neumann.UniformRowBound indices
    (finiteFifthTail indices matrix coefficients exponent)
    fifthTailCap
finiteFifthTailUniformCap indices matrix coefficients exponent matrixRows row =
  ℚP.≤-trans
    (finiteFifthTailRowBound
      indices matrix coefficients exponent matrixRows row)
    (geometricMajorantBelowFifthTailCap exponent)

reducedGhostMatrixLogFifthTailLevel : ProofLevel
reducedGhostMatrixLogFifthTailLevel = machineChecked
