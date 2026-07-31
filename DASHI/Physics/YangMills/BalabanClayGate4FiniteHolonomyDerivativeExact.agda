module DASHI.Physics.YangMills.BalabanClayGate4FiniteHolonomyDerivativeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact left-trivialized derivative of a finite lattice holonomy.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Under the left perturbation convention U_e(t)=exp(t A_e)U_e,
--
--   D^L(U_{e1}...U_{en})[A]
--     = A_{e1} + Ad_{U_{e1}} A_{e2} + ... .
--
-- The recursion below is the exact finite formula.  It also proves that a
-- variation which vanishes on every path edge has zero holonomy derivative;
-- this is the algebraic support theorem used by the CMP109 kernel.
------------------------------------------------------------------------

record HolonomyDifferentialAlgebra
    (Group Lie : Set) : Set₁ where
  field
    identityGroup : Group
    multiplyGroup : Group → Group → Group

    zeroLie : Lie
    addLie : Lie → Lie → Lie
    adjoint : Group → Lie → Lie

    addZeroLeft : ∀ vector → addLie zeroLie vector ≡ vector
    addZeroRight : ∀ vector → addLie vector zeroLie ≡ vector
    adjointZero : ∀ group → adjoint group zeroLie ≡ zeroLie

open HolonomyDifferentialAlgebra public

holonomy :
  ∀ {Edge Group Lie} →
  HolonomyDifferentialAlgebra Group Lie →
  (Edge → Group) → List Edge → Group
holonomy algebra field [] = identityGroup algebra
holonomy algebra field (edge ∷ edges) =
  multiplyGroup algebra (field edge) (holonomy algebra field edges)

leftTrivializedHolonomyDerivative :
  ∀ {Edge Group Lie} →
  HolonomyDifferentialAlgebra Group Lie →
  (Edge → Group) → (Edge → Lie) → List Edge → Lie
leftTrivializedHolonomyDerivative algebra field variation [] =
  zeroLie algebra
leftTrivializedHolonomyDerivative algebra field variation (edge ∷ edges) =
  addLie algebra
    (variation edge)
    (adjoint algebra (field edge)
      (leftTrivializedHolonomyDerivative algebra field variation edges))

record All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

variationZeroOnPath :
  ∀ {Edge Group Lie}
    (algebra : HolonomyDifferentialAlgebra Group Lie)
    (field : Edge → Group) (variation : Edge → Lie)
    (edges : List Edge) →
  All (λ edge → variation edge ≡ zeroLie algebra) edges →
  leftTrivializedHolonomyDerivative algebra field variation edges
  ≡ zeroLie algebra
variationZeroOnPath algebra field variation [] allNil = refl
variationZeroOnPath algebra field variation (edge ∷ edges)
    (allCons edgeZero restZero) =
  trans
    (cong
      (addLie algebra (variation edge))
      (trans
        (cong (adjoint algebra (field edge))
          (variationZeroOnPath algebra field variation edges restZero))
        (adjointZero algebra (field edge))))
    (trans
      (cong (λ head → addLie algebra head (zeroLie algebra)) edgeZero)
      (addZeroLeft algebra (zeroLie algebra)))

finiteHolonomyDefinitionLevel : ProofLevel
finiteHolonomyDefinitionLevel = computed

finiteHolonomyDerivativeFormulaLevel : ProofLevel
finiteHolonomyDerivativeFormulaLevel = computed

finiteHolonomyDerivativeSupportLevel : ProofLevel
finiteHolonomyDerivativeSupportLevel = machineChecked

physicalLeftPerturbationCalculusInputsLevel : ProofLevel
physicalLeftPerturbationCalculusInputsLevel = conditional
