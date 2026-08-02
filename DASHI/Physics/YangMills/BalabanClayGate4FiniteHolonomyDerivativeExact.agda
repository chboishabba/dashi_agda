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
  ∀ {Edge Group Lie : Set} →
  HolonomyDifferentialAlgebra Group Lie →
  (Edge → Group) → List Edge → Group
holonomy algebra connection [] = identityGroup algebra
holonomy algebra connection (edge ∷ edges) =
  multiplyGroup algebra (connection edge) (holonomy algebra connection edges)

leftTrivializedHolonomyDerivative :
  ∀ {Edge Group Lie : Set} →
  HolonomyDifferentialAlgebra Group Lie →
  (Edge → Group) → (Edge → Lie) → List Edge → Lie
leftTrivializedHolonomyDerivative algebra connection variation [] =
  zeroLie algebra
leftTrivializedHolonomyDerivative algebra connection variation (edge ∷ edges) =
  addLie algebra
    (variation edge)
    (adjoint algebra (connection edge)
      (leftTrivializedHolonomyDerivative algebra connection variation edges))

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

variationZeroOnPath :
  ∀ {Edge Group Lie : Set}
    (algebra : HolonomyDifferentialAlgebra Group Lie)
    (connection : Edge → Group) (variation : Edge → Lie)
    (edges : List Edge) →
  All (λ edge → variation edge ≡ zeroLie algebra) edges →
  leftTrivializedHolonomyDerivative algebra connection variation edges
  ≡ zeroLie algebra
variationZeroOnPath algebra connection variation [] allNil = refl
variationZeroOnPath algebra connection variation (edge ∷ edges)
    (allCons edgeZero restZero) =
  trans
    (cong
      (addLie algebra (variation edge))
      (trans
        (cong (adjoint algebra (connection edge))
          (variationZeroOnPath algebra connection variation edges restZero))
        (adjointZero algebra (connection edge))))
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
