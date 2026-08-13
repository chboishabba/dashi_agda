module DASHI.Physics.YangMills.BalabanYM4DifferentiatedMinimizerGreenResponseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact linear-response identity needed by RG1d.  Once the literal
-- differentiated constrained Euler--Lagrange equation has the form
--
--       H deltaA + s = 0
--
-- and G is a LEFT inverse of H on the selected finite tangent carrier, finite
-- Fubini/distributivity gives G(H v)=v, hence
--
--       deltaA = - G s.
--
-- No function extensionality postulate, implicit-function theorem, or new
-- inverse construction is used.  This is the algebraic bridge to the already
-- proved physical Combes--Thomas remote-response estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

Vector : Set → Set
Vector Index = Index → ℚ

Matrix : Set → Set
Matrix Index = Index → Index → ℚ

matrixApply :
  ∀ {Index : Set} → List Index → Matrix Index → Vector Index → Vector Index
matrixApply indices matrix vector row =
  Sums.sumRational indices (λ column → matrix row column * vector column)

LeftInverse :
  ∀ {Index : Set} →
  List Index → Matrix Index → Matrix Index → Matrix Index → Set
LeftInverse indices identity inverse operator =
  ∀ row column →
  Sums.sumRational indices
    (λ middle → inverse row middle * operator middle column)
  ≡ identity row column

record FiniteIdentityAction (Index : Set) : Set₁ where
  field
    indices : List Index
    identity : Matrix Index
    identityActs : ∀ vector row →
      matrixApply indices identity vector row ≡ vector row

open FiniteIdentityAction public

sumRightScale :
  ∀ {Index : Set} coefficient (values : List Index) (term : Index → ℚ) →
  Sums.sumRational values (λ value → term value * coefficient)
  ≡ Sums.sumRational values term * coefficient
sumRightScale coefficient values term =
  trans
    (Sums.sumRationalCong values _ _
      (λ value → ℚP.*-comm (term value) coefficient))
    (trans
      (Sums.sumRationalScale coefficient values term)
      (ℚP.*-comm coefficient (Sums.sumRational values term)))

scaleSumOnRight :
  ∀ {Index : Set} coefficient (values : List Index) (term : Index → ℚ) →
  coefficient * Sums.sumRational values term
  ≡ Sums.sumRational values (λ value → coefficient * term value)
scaleSumOnRight coefficient values term =
  sym (Sums.sumRationalScale coefficient values term)

matrixApplyNegate :
  ∀ {Index : Set} indices (matrix : Matrix Index) vector row →
  matrixApply indices matrix (λ index → - vector index) row
  ≡ - matrixApply indices matrix vector row
matrixApplyNegate [] matrix vector row = refl
matrixApplyNegate (column ∷ columns) matrix vector row
  rewrite matrixApplyNegate columns matrix vector row = ℚRing.solve []

matrixApplyCompositionExpand :
  ∀ {Index : Set} indices (left right : Matrix Index) vector row →
  matrixApply indices left (matrixApply indices right vector) row
  ≡ Sums.sumRational indices
      (λ column →
        Sums.sumRational indices
          (λ middle → left row middle * right middle column)
        * vector column)
matrixApplyCompositionExpand indices left right vector row =
  let
    expandInner :
      Sums.sumRational indices
        (λ middle →
          left row middle * matrixApply indices right vector middle)
      ≡ Sums.sumRational indices
          (λ middle →
            Sums.sumRational indices
              (λ column →
                left row middle * (right middle column * vector column)))
    expandInner = Sums.sumRationalCong indices _ _
      (λ middle →
        scaleSumOnRight
          (left row middle)
          indices
          (λ column → right middle column * vector column))

    swap :
      Sums.sumRational indices
        (λ middle →
          Sums.sumRational indices
            (λ column →
              left row middle * (right middle column * vector column)))
      ≡ Sums.sumRational indices
          (λ column →
            Sums.sumRational indices
              (λ middle →
                left row middle * (right middle column * vector column)))
    swap = Fubini.sumSwap indices indices
      (λ middle column →
        left row middle * (right middle column * vector column))

    factorColumn : ∀ column →
      Sums.sumRational indices
        (λ middle →
          left row middle * (right middle column * vector column))
      ≡ Sums.sumRational indices
          (λ middle → left row middle * right middle column)
        * vector column
    factorColumn column =
      trans
        (Sums.sumRationalCong indices _ _
          (λ middle → ℚP.*-assoc
            (left row middle) (right middle column) (vector column)))
        (sumRightScale
          (vector column) indices
          (λ middle → left row middle * right middle column))
  in
  trans expandInner
    (trans swap
      (Sums.sumRationalCong indices _ _ factorColumn))

greenAfterHessianFromLeftInverse :
  ∀ {Index}
    (finite : FiniteIdentityAction Index)
    (hessian green : Matrix Index) →
  LeftInverse (indices finite) (identity finite) green hessian →
  ∀ vector row →
  matrixApply (indices finite) green
    (matrixApply (indices finite) hessian vector) row
  ≡ vector row
greenAfterHessianFromLeftInverse finite hessian green leftInverse vector row =
  trans
    (matrixApplyCompositionExpand
      (indices finite) green hessian vector row)
    (trans
      (Sums.sumRationalCong (indices finite) _ _
        (λ column →
          cong (_* vector column) (leftInverse row column)))
      (identityActs finite vector row))

record DifferentiatedMinimizerSystem (Index : Set) : Set₁ where
  field
    finite : FiniteIdentityAction Index
    hessian green : Matrix Index
    deltaA source : Vector Index

    greenLeftInverse :
      LeftInverse (indices finite) (identity finite) green hessian

    differentiatedEulerLagrange : ∀ row →
      matrixApply (indices finite) hessian deltaA row + source row ≡ 0ℚ

open DifferentiatedMinimizerSystem public

hessianResponseIsNegativeSource :
  ∀ {Index} (system : DifferentiatedMinimizerSystem Index) row →
  matrixApply (indices (finite system)) (hessian system) (deltaA system) row
  ≡ - source system row
hessianResponseIsNegativeSource system row =
  let
    equation = differentiatedEulerLagrange system row
    h = matrixApply (indices (finite system))
          (hessian system) (deltaA system) row
    s = source system row
  in
  trans
    (sym (ℚRing.solve-∀ h s : h ≡ (h + s) - s))
    (trans
      (cong (_- s) equation)
      (ℚRing.solve-∀ s))

greenAppliedToHessianResponse :
  ∀ {Index} (system : DifferentiatedMinimizerSystem Index) row →
  matrixApply (indices (finite system)) (green system)
    (matrixApply (indices (finite system))
      (hessian system) (deltaA system)) row
  ≡ matrixApply (indices (finite system)) (green system)
      (λ coordinate → - source system coordinate) row
greenAppliedToHessianResponse system row =
  Sums.sumRationalCong
    (indices (finite system)) _ _
    (λ column →
      cong ((green system row column) *_)
        (hessianResponseIsNegativeSource system column))

differentiatedMinimizerGreenResponse :
  ∀ {Index}
    (system : DifferentiatedMinimizerSystem Index) →
  ∀ row →
  deltaA system row
  ≡ - matrixApply (indices (finite system))
      (green system) (source system) row
differentiatedMinimizerGreenResponse system row =
  trans
    (sym
      (greenAfterHessianFromLeftInverse
        (finite system) (hessian system) (green system)
        (greenLeftInverse system) (deltaA system) row))
    (trans
      (greenAppliedToHessianResponse system row)
      (matrixApplyNegate
        (indices (finite system)) (green system) (source system) row))

ym4DifferentiatedMinimizerResponseAlgebraLevel : ProofLevel
ym4DifferentiatedMinimizerResponseAlgebraLevel = machineChecked

-- Remaining RG1d physical inputs are now only the literal identification of
-- H, G, deltaA and s with the differentiated selected minimizer, plus remote
-- support of s.  The response identity itself is no longer conditional.
ym4DifferentiatedMinimizerPhysicalIdentificationLevel : ProofLevel
ym4DifferentiatedMinimizerPhysicalIdentificationLevel = conditional
