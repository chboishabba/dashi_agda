module DASHI.Physics.YangMills.BalabanReducedGhostFourthOrderRowContractionExact where

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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Round61 already constructs the SAME reduced physical perturbation matrix
--
--     R(g) = M_A M_0^{-1} - I
--
-- and its source-native coefficient matrices X1,...,X4.  The existing
-- Neumann/logarithm theorem says the remaining convergence input is a strict
-- row-mass contraction q < 1 for this same R(g).
--
-- This file removes one more layer of analytic ambiguity.  If the actual
-- matrix has the pointwise expansion
--
--   R = g X1 + g^2 X2 + g^3 X3 + g^4 X4 + E5,
--
-- then finite triangle inequality proves directly
--
--   rowMass(R)
--     <= |g| b1 + |g^2| b2 + |g^3| b3 + |g^4| b4 + b5
--
-- from uniform row bounds rowMass(Xj)<=bj and rowMass(E5)<=b5.
--
-- Hence the physical convergence producer is no longer an opaque q-bound:
-- it is enough to bound the FOUR ALREADY-CONSTRUCTED coefficient matrices and
-- the genuine fifth-order tail on the selected Bishop ball, then prove the
-- displayed scalar budget is < 1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Contraction

matrixAdd : ∀ {Index : Set} →
  Matrix.Matrix Index → Matrix.Matrix Index → Matrix.Matrix Index
matrixAdd left right row column = left row column + right row column

matrixScale : ∀ {Index : Set} →
  ℚ → Matrix.Matrix Index → Matrix.Matrix Index
matrixScale scalar matrix row column = scalar * matrix row column

rowMass : ∀ {Index : Set} →
  List Index → Matrix.Matrix Index → Index → ℚ
rowMass = Contraction.rowMass

rowMassAddUpper :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) row →
  rowMass indices (matrixAdd left right) row
  ≤ rowMass indices left row + rowMass indices right row
rowMassAddUpper indices left right row =
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
  subst
    (λ upper → rowMass indices (matrixAdd left right) row ≤ upper)
    split pointwise

rowMassScaleExact :
  ∀ {Index : Set} (indices : List Index)
    scalar (matrix : Matrix.Matrix Index) row →
  rowMass indices (matrixScale scalar matrix) row
  ≡ ∣ scalar ∣ * rowMass indices matrix row
rowMassScaleExact indices scalar matrix row =
  trans
    (Sums.sumRationalCong indices _ _
      (λ column → ℚP.∣p*q∣≡∣p∣*∣q∣ scalar (matrix row column)))
    (Sums.sumRationalScale ∣ scalar ∣ indices
      (λ column → ∣ matrix row column ∣))

scaledRowBound :
  ∀ {Index : Set} (indices : List Index)
    scalar (matrix : Matrix.Matrix Index) bound row →
  rowMass indices matrix row ≤ bound →
  rowMass indices (matrixScale scalar matrix) row
  ≤ ∣ scalar ∣ * bound
scaledRowBound indices scalar matrix bound row matrixBound =
  subst
    (λ lower → lower ≤ ∣ scalar ∣ * bound)
    (sym (rowMassScaleExact indices scalar matrix row))
    (Norm.scaleNonnegative
      ∣ scalar ∣ (ℚP.0≤∣p∣ scalar) matrixBound)

rowMassCong :
  ∀ {Index : Set} (indices : List Index)
    (left right : Matrix.Matrix Index) →
  (∀ row column → left row column ≡ right row column) →
  ∀ row → rowMass indices left row ≡ rowMass indices right row
rowMassCong indices left right pointwise row =
  Sums.sumRationalCong indices _ _
    (λ column → cong ∣_∣ (pointwise row column))

record FourthOrderReducedGhostExpansion (Index : Set) : Set₁ where
  field
    indices : List Index
    coupling : ℚ
    actual X1 X2 X3 X4 tail : Matrix.Matrix Index
    exactFourthOrderExpansion : ∀ row column →
      actual row column
      ≡ matrixAdd
          (matrixScale coupling X1)
          (matrixAdd
            (matrixScale (coupling * coupling) X2)
            (matrixAdd
              (matrixScale (coupling * coupling * coupling) X3)
              (matrixAdd
                (matrixScale
                  (coupling * coupling * coupling * coupling) X4)
                tail)))
          row column
    b1 b2 b3 b4 b5 : ℚ
    X1RowBound : ∀ row → rowMass indices X1 row ≤ b1
    X2RowBound : ∀ row → rowMass indices X2 row ≤ b2
    X3RowBound : ∀ row → rowMass indices X3 row ≤ b3
    X4RowBound : ∀ row → rowMass indices X4 row ≤ b4
    tailRowBound : ∀ row → rowMass indices tail row ≤ b5

open FourthOrderReducedGhostExpansion public

contractionBudget :
  ∀ {Index : Set} → FourthOrderReducedGhostExpansion Index → ℚ
contractionBudget dataSet =
  ∣ coupling dataSet ∣ * b1 dataSet
  + (∣ coupling dataSet * coupling dataSet ∣ * b2 dataSet
  + (∣ coupling dataSet * coupling dataSet * coupling dataSet ∣ * b3 dataSet
  + (∣ coupling dataSet * coupling dataSet * coupling dataSet * coupling dataSet ∣
      * b4 dataSet
  + b5 dataSet)))

expandedMatrix :
  ∀ {Index : Set} → FourthOrderReducedGhostExpansion Index → Matrix.Matrix Index
expandedMatrix dataSet =
  matrixAdd
    (matrixScale (coupling dataSet) (X1 dataSet))
    (matrixAdd
      (matrixScale
        (coupling dataSet * coupling dataSet) (X2 dataSet))
      (matrixAdd
        (matrixScale
          (coupling dataSet * coupling dataSet * coupling dataSet)
          (X3 dataSet))
        (matrixAdd
          (matrixScale
            (coupling dataSet * coupling dataSet
              * coupling dataSet * coupling dataSet)
            (X4 dataSet))
          (tail dataSet))))

actualEqualsExpandedRowMass :
  ∀ {Index : Set} (dataSet : FourthOrderReducedGhostExpansion Index) row →
  rowMass (indices dataSet) (actual dataSet) row
  ≡ rowMass (indices dataSet) (expandedMatrix dataSet) row
actualEqualsExpandedRowMass dataSet =
  rowMassCong
    (indices dataSet)
    (actual dataSet)
    (expandedMatrix dataSet)
    (exactFourthOrderExpansion dataSet)

fourthOrderRowContractionBound :
  ∀ {Index : Set} (dataSet : FourthOrderReducedGhostExpansion Index) row →
  rowMass (indices dataSet) (actual dataSet) row
  ≤ contractionBudget dataSet
fourthOrderRowContractionBound dataSet row =
  let
    g = coupling dataSet
    ixs = indices dataSet
    t1 = matrixScale g (X1 dataSet)
    t2 = matrixScale (g * g) (X2 dataSet)
    t3 = matrixScale (g * g * g) (X3 dataSet)
    t4 = matrixScale (g * g * g * g) (X4 dataSet)
    b1' = ∣ g ∣ * b1 dataSet
    b2' = ∣ g * g ∣ * b2 dataSet
    b3' = ∣ g * g * g ∣ * b3 dataSet
    b4' = ∣ g * g * g * g ∣ * b4 dataSet
    t1Bound : rowMass ixs t1 row ≤ b1'
    t1Bound = scaledRowBound ixs g (X1 dataSet) (b1 dataSet) row
      (X1RowBound dataSet row)
    t2Bound : rowMass ixs t2 row ≤ b2'
    t2Bound = scaledRowBound ixs (g * g) (X2 dataSet) (b2 dataSet) row
      (X2RowBound dataSet row)
    t3Bound : rowMass ixs t3 row ≤ b3'
    t3Bound = scaledRowBound ixs (g * g * g) (X3 dataSet) (b3 dataSet) row
      (X3RowBound dataSet row)
    t4Bound : rowMass ixs t4 row ≤ b4'
    t4Bound = scaledRowBound ixs (g * g * g * g) (X4 dataSet) (b4 dataSet) row
      (X4RowBound dataSet row)
    fourthAndTail :
      rowMass ixs (matrixAdd t4 (tail dataSet)) row ≤ b4' + b5 dataSet
    fourthAndTail = ℚP.≤-trans
      (rowMassAddUpper ixs t4 (tail dataSet) row)
      (ℚP.+-mono-≤ t4Bound (tailRowBound dataSet row))
    thirdTail :
      rowMass ixs (matrixAdd t3 (matrixAdd t4 (tail dataSet))) row
      ≤ b3' + (b4' + b5 dataSet)
    thirdTail = ℚP.≤-trans
      (rowMassAddUpper ixs t3 (matrixAdd t4 (tail dataSet)) row)
      (ℚP.+-mono-≤ t3Bound fourthAndTail)
    secondTail :
      rowMass ixs
        (matrixAdd t2 (matrixAdd t3 (matrixAdd t4 (tail dataSet)))) row
      ≤ b2' + (b3' + (b4' + b5 dataSet))
    secondTail = ℚP.≤-trans
      (rowMassAddUpper ixs t2
        (matrixAdd t3 (matrixAdd t4 (tail dataSet))) row)
      (ℚP.+-mono-≤ t2Bound thirdTail)
    firstTail :
      rowMass ixs
        (matrixAdd t1
          (matrixAdd t2 (matrixAdd t3 (matrixAdd t4 (tail dataSet))))) row
      ≤ b1' + (b2' + (b3' + (b4' + b5 dataSet)))
    firstTail = ℚP.≤-trans
      (rowMassAddUpper ixs t1
        (matrixAdd t2 (matrixAdd t3 (matrixAdd t4 (tail dataSet)))) row)
      (ℚP.+-mono-≤ t1Bound secondTail)
  in
  subst
    (λ lower → lower ≤ contractionBudget dataSet)
    (sym (actualEqualsExpandedRowMass dataSet row))
    firstTail

uniformFourthOrderRowContractionBound :
  ∀ {Index : Set} (dataSet : FourthOrderReducedGhostExpansion Index) →
  Contraction.UniformRowBound
    (indices dataSet) (actual dataSet) (contractionBudget dataSet)
uniformFourthOrderRowContractionBound dataSet =
  fourthOrderRowContractionBound dataSet

reducedGhostFourthOrderRowBudgetLevel : ProofLevel
reducedGhostFourthOrderRowBudgetLevel = machineChecked

physicalSameObjectFourthOrderExpansionLevel : ProofLevel
physicalSameObjectFourthOrderExpansionLevel = conditional

physicalReducedGhostFifthOrderTailRowBoundLevel : ProofLevel
physicalReducedGhostFifthOrderTailRowBoundLevel = conditional

physicalReducedGhostBudgetStrictlyBelowOneLevel : ProofLevel
physicalReducedGhostBudgetStrictlyBelowOneLevel = conditional
