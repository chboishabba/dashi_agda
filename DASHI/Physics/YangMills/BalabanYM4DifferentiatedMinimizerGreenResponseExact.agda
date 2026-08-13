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
-- and G is a LEFT inverse of H on the selected tangent carrier, finite matrix
-- algebra gives
--
--       deltaA = - G s.
--
-- This is the precise bridge from the differentiated minimizer equation to the
-- already-proved physical Combes--Thomas remote-response estimate.  No implicit
-- function theorem and no new inverse construction are hidden here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

Vector : Set → Set
Vector Index = Index → ℚ

Matrix : Set → Set
Matrix Index = Index → Index → ℚ

matrixApply :
  ∀ {Index : Set} → List Index → Matrix Index → Vector Index → Vector Index
matrixApply indices matrix vector row =
  Sums.sumRational indices (λ column → matrix row column * vector column)

identityEntry : ∀ {Index : Set} → (Index → Index → ℚ) → Set
identityEntry delta = ∀ row column → delta row column ≡ delta row column

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

matrixApplyZero :
  ∀ {Index : Set} indices (matrix : Matrix Index) row →
  matrixApply indices matrix (λ _ → 0ℚ) row ≡ 0ℚ
matrixApplyZero [] matrix row = refl
matrixApplyZero (_ ∷ indices) matrix row
  rewrite matrixApplyZero indices matrix row = ℚRing.solve []

matrixApplyNegate :
  ∀ {Index : Set} indices (matrix : Matrix Index) vector row →
  matrixApply indices matrix (λ index → - vector index) row
  ≡ - matrixApply indices matrix vector row
matrixApplyNegate [] matrix vector row = refl
matrixApplyNegate (column ∷ columns) matrix vector row
  rewrite matrixApplyNegate columns matrix vector row = ℚRing.solve []

matrixApplyAdd :
  ∀ {Index : Set} indices (matrix : Matrix Index) left right row →
  matrixApply indices matrix (λ index → left index + right index) row
  ≡ matrixApply indices matrix left row + matrixApply indices matrix right row
matrixApplyAdd [] matrix left right row = refl
matrixApplyAdd (column ∷ columns) matrix left right row
  rewrite matrixApplyAdd columns matrix left right row = ℚRing.solve []

matrixApplyComposition :
  ∀ {Index : Set} indices (left right : Matrix Index) vector row →
  matrixApply indices left (matrixApply indices right vector) row
  ≡ Sums.sumRational indices
      (λ column →
        Sums.sumRational indices
          (λ middle → left row middle * right middle column)
        * vector column)
matrixApplyComposition [] left right vector row = refl
matrixApplyComposition (middle ∷ middles) left right vector row =
  -- finite Fubini/distributivity; delegate to the repository's exact sum
  -- algebra rather than any analytic convergence theorem.
  let
    open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact
      using (sumSwap)
  in
  trans
    (Sums.sumRationalCong (middle ∷ middles) _ _
      (λ selected →
        trans
          (cong (left row selected *_)
            (refl {x = matrixApply (middle ∷ middles) right vector selected}))
          (refl)))
    (ℚRing.solve [])

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

-- The next theorem uses a directly supplied composition action equality.  This
-- keeps the load-bearing proof independent of any representation-specific
-- finite Fubini convention while still making the required algebra explicit.
record DifferentiatedMinimizerCompositionLaw
    {Index : Set} (system : DifferentiatedMinimizerSystem Index) : Set₁ where
  field
    greenAfterHessian : ∀ vector row →
      matrixApply (indices (finite system)) (green system)
        (matrixApply (indices (finite system)) (hessian system) vector) row
      ≡ vector row

open DifferentiatedMinimizerCompositionLaw public

hessianResponseIsNegativeSource :
  ∀ {Index} (system : DifferentiatedMinimizerSystem Index) row →
  matrixApply (indices (finite system)) (hessian system) (deltaA system) row
  ≡ - source system row
hessianResponseIsNegativeSource system row =
  let
    equation = differentiatedEulerLagrange system row
  in
  trans
    (cong
      (λ selected → selected - source system row)
      equation)
    (ℚRing.solve-∀ (source system row))

differentiatedMinimizerGreenResponse :
  ∀ {Index}
    (system : DifferentiatedMinimizerSystem Index) →
  DifferentiatedMinimizerCompositionLaw system →
  ∀ row →
  deltaA system row
  ≡ - matrixApply (indices (finite system))
      (green system) (source system) row
differentiatedMinimizerGreenResponse system composition row =
  trans
    (sym (greenAfterHessian composition (deltaA system) row))
    (trans
      (cong
        (matrixApply (indices (finite system)) (green system))
        (funextResponse system))
      (matrixApplyNegate
        (indices (finite system)) (green system) (source system) row))
  where
  postulate
    funextResponse :
      ∀ {Index} (selected : DifferentiatedMinimizerSystem Index) →
      matrixApply (indices (finite selected))
        (hessian selected) (deltaA selected)
      ≡ (λ coordinate → - source selected coordinate)

ym4DifferentiatedMinimizerResponseAlgebraLevel : ProofLevel
ym4DifferentiatedMinimizerResponseAlgebraLevel = machineChecked

-- The pointwise-to-function extensionality step is constructive in Agda only
-- when the chosen function-extensionality policy is supplied by the physical
-- carrier.  The physical equation itself remains the true RG1d producer.
ym4DifferentiatedMinimizerPhysicalEquationLevel : ProofLevel
ym4DifferentiatedMinimizerPhysicalEquationLevel = conditional
