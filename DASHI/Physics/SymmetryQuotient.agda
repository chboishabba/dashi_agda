module DASHI.Physics.SymmetryQuotient where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.PhysicalTheory as PT

record Action {ℓ : Level} (G X : Set ℓ) : Set (lsuc ℓ) where
  field
    _∙_ : G → X → X

record SymmetricTheory (ℓ : Level) : Set (lsuc ℓ) where
  field
    base  : PT.PhysicalTheory ℓ

    Group : Set ℓ
    act   : Group → PT.State base → PT.State base

    step-equivariant :
      ∀ g x → PT.step base (act g x) ≡ act g (PT.step base x)

    inv-invariant :
      ∀ g x → PT.Inv base x → PT.Inv base (act g x)

record PhysicalEquivalence {ℓ : Level}
  (S : SymmetricTheory ℓ) : Set (lsuc ℓ) where
  open SymmetricTheory S
  field
    _≈phys_ : PT.State base → PT.State base → Set ℓ

    orbit→phys :
      ∀ g x → x ≈phys act g x

    step-respects :
      ∀ {x y} → x ≈phys y → PT.step base x ≈phys PT.step base y

record QuotientedTheory (ℓ : Level) : Set (lsuc ℓ) where
  field
    sym    : SymmetricTheory ℓ
    physEq : PhysicalEquivalence sym

    PhysState : Set ℓ
    repr      : PhysState → PT.State (SymmetricTheory.base sym)
    classOf   : PT.State (SymmetricTheory.base sym) → PhysState

    class-sound :
      ∀ x y →
      PhysicalEquivalence._≈phys_ physEq x y →
      classOf x ≡ classOf y

open QuotientedTheory public
