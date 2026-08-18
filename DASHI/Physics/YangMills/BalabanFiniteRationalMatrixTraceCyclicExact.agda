module DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Prove the finite rational matrix product and cyclic trace laws directly on
-- the repository's finite folds.  No abstract finite-dimensional linear
-- algebra package is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre

Matrix : Set → Set
Matrix Index = Index → Index → ℚ

matrixProduct :
  ∀ {Index} → List Index → Matrix Index → Matrix Index → Matrix Index
matrixProduct indices left right row column =
  Sums.sumRational indices
    (λ middle → left row middle * right middle column)

matrixTrace : ∀ {Index} → List Index → Matrix Index → ℚ
matrixTrace indices matrix =
  Sums.sumRational indices (λ index → matrix index index)

matrixProductAssociative :
  ∀ {Index} (indices : List Index)
    (first second third : Matrix Index) row column →
  matrixProduct indices (matrixProduct indices first second) third row column
  ≡ matrixProduct indices first (matrixProduct indices second third) row column
matrixProductAssociative indices first second third row column =
  trans
    (Sums.sumRationalCong indices _ _
      (λ middle2 →
        Fibre.sumRationalScaleRight
          (third middle2 column)
          indices
          (λ middle1 → first row middle1 * second middle1 middle2)))
    (trans
      (Fubini.sumSwap indices indices
        (λ middle2 middle1 →
          (first row middle1 * second middle1 middle2)
          * third middle2 column))
      (Sums.sumRationalCong indices _ _
        (λ middle1 →
          trans
            (Sums.sumRationalCong indices _ _
              (λ middle2 →
                ℚP.*-assoc
                  (first row middle1)
                  (second middle1 middle2)
                  (third middle2 column)))
            (Sums.sumRationalScale
              (first row middle1)
              indices
              (λ middle2 →
                second middle1 middle2 * third middle2 column)))))

traceProductUnfold :
  ∀ {Index} (indices : List Index) left right →
  matrixTrace indices (matrixProduct indices left right)
  ≡ Sums.sumRational indices
      (λ row → Sums.sumRational indices
        (λ column → left row column * right column row))
traceProductUnfold indices left right = refl

finiteMatrixTraceCyclic :
  ∀ {Index} (indices : List Index) (left right : Matrix Index) →
  matrixTrace indices (matrixProduct indices left right)
  ≡ matrixTrace indices (matrixProduct indices right left)
finiteMatrixTraceCyclic indices left right =
  trans
    (Fubini.sumSwap indices indices
      (λ row column → left row column * right column row))
    (Sums.sumRationalCong indices _ _
      (λ column →
        Sums.sumRationalCong indices _ _
          (λ row → ℚP.*-comm
            (left row column) (right column row))))

finiteRationalMatrixProductAssociativityLevel : ProofLevel
finiteRationalMatrixProductAssociativityLevel = machineChecked

finiteRationalMatrixTraceDefinitionLevel : ProofLevel
finiteRationalMatrixTraceDefinitionLevel = machineChecked

finiteRationalMatrixTraceCyclicityLevel : ProofLevel
finiteRationalMatrixTraceCyclicityLevel = machineChecked
