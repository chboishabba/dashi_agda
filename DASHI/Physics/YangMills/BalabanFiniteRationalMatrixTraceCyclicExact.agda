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
-- Prove the cyclic two-factor trace law directly on the repository's finite
-- rational folds.  No abstract finite-dimensional linear algebra package is
-- required:
--
--       tr(A B) = sum_i sum_j A_ij B_ji
--               = sum_j sum_i B_ji A_ij
--               = tr(B A).
--
-- The only ingredients are finite-sum Fubini and commutativity of rational
-- multiplication.  This removes cyclic trace identities as independent ghost
-- determinant inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

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

finiteRationalMatrixTraceDefinitionLevel : ProofLevel
finiteRationalMatrixTraceDefinitionLevel = machineChecked

finiteRationalMatrixTraceCyclicityLevel : ProofLevel
finiteRationalMatrixTraceCyclicityLevel = machineChecked
