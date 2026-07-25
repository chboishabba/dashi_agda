module DASHI.Physics.Closure.NSPeriodicFiniteTriadPartition where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFinitePythagoreanSum as Finite
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact finite partition of literal Galerkin triads into LH, HL and HH.
--
-- Geometry decides one of the three classes for every near interaction.  This
-- module proves by list induction that the literal total fold is exactly the sum
-- of the three class folds.  No estimate, cutoff constant, or PDE assumption is
-- used in the partition theorem.
------------------------------------------------------------------------

data NearClass : Set where
  lowHigh highLow highHigh : NearClass

record ClassifiedNearFamily
    {i : Level}
    (A : AbsorptionArithmetic)
    (Item : Set i) : Set (lsuc i) where
  field
    classify : Item → NearClass
    contribution : Item → Scalar A

open ClassifiedNearFamily public

nearTotal :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  ClassifiedNearFamily A Item → List Item → Scalar A
nearTotal {A = A} F [] = zero A
nearTotal {A = A} F (item ∷ items) =
  _+_ A (contribution F item) (nearTotal F items)

nearLowHigh nearHighLow nearHighHigh :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  ClassifiedNearFamily A Item → List Item → Scalar A
nearLowHigh {A = A} F [] = zero A
nearLowHigh {A = A} F (item ∷ items) with classify F item
... | lowHigh = _+_ A (contribution F item) (nearLowHigh F items)
... | highLow = nearLowHigh F items
... | highHigh = nearLowHigh F items

nearHighLow {A = A} F [] = zero A
nearHighLow {A = A} F (item ∷ items) with classify F item
... | lowHigh = nearHighLow F items
... | highLow = _+_ A (contribution F item) (nearHighLow F items)
... | highHigh = nearHighLow F items

nearHighHigh {A = A} F [] = zero A
nearHighHigh {A = A} F (item ∷ items) with classify F item
... | lowHigh = nearHighHigh F items
... | highLow = nearHighHigh F items
... | highHigh = _+_ A (contribution F item) (nearHighHigh F items)

zeroTriple :
  (A : AbsorptionArithmetic) →
  zero A ≡ _+_ A (_+_ A (zero A) (zero A)) (zero A)
zeroTriple A =
  sym
    (trans
      (cong (λ first → _+_ A first (zero A))
        (addZeroLeft A (zero A)))
      (addZeroLeft A (zero A)))

headIntoLowHigh :
  (A : AbsorptionArithmetic) →
  ∀ head lh hl hh →
  _+_ A head (_+_ A (_+_ A lh hl) hh)
  ≡ _+_ A (_+_ A (_+_ A head lh) hl) hh
headIntoLowHigh A head lh hl hh =
  trans
    (cong (λ tail → _+_ A head tail)
      (addAssociative A lh hl hh |> sym))
    (trans
      (addAssociative A head (_+_ A lh hl) hh |> sym)
      (cong (λ first → _+_ A first hh)
        (addAssociative A head lh hl |> sym)))
  where
  infixl 0 _|>_
  _|>_ : ∀ {X Y : Set} → X → (X → Y) → Y
  x |> f = f x

headIntoHighLow :
  (A : AbsorptionArithmetic) →
  ∀ head lh hl hh →
  _+_ A head (_+_ A (_+_ A lh hl) hh)
  ≡ _+_ A (_+_ A lh (_+_ A head hl)) hh
headIntoHighLow A head lh hl hh =
  trans
    (headIntoLowHigh A head lh hl hh)
    (cong (λ first → _+_ A first hh)
      (trans
        (addAssociative A head lh hl)
        (trans
          (cong (λ tail → _+_ A tail hl)
            (addCommutative A head lh))
          (addAssociative A lh head hl |> sym))))
  where
  infixl 0 _|>_
  _|>_ : ∀ {X Y : Set} → X → (X → Y) → Y
  x |> f = f x

headIntoHighHigh :
  (A : AbsorptionArithmetic) →
  ∀ head lh hl hh →
  _+_ A head (_+_ A (_+_ A lh hl) hh)
  ≡ _+_ A (_+_ A lh hl) (_+_ A head hh)
headIntoHighHigh A head lh hl hh =
  trans
    (cong (λ tail → _+_ A head tail)
      (addAssociative A lh hl hh |> sym))
    (trans
      (addAssociative A head (_+_ A lh hl) hh |> sym)
      (trans
        (cong (λ first → _+_ A first hh)
          (addCommutative A head (_+_ A lh hl)))
        (addAssociative A (_+_ A lh hl) head hh)))
  where
  infixl 0 _|>_
  _|>_ : ∀ {X Y : Set} → X → (X → Y) → Y
  x |> f = f x

finiteNearTriadDecomposition :
  ∀ {i} {A : AbsorptionArithmetic} {Item : Set i} →
  (F : ClassifiedNearFamily A Item) →
  ∀ items →
  nearTotal F items
  ≡ _+_ A
      (_+_ A (nearLowHigh F items) (nearHighLow F items))
      (nearHighHigh F items)
finiteNearTriadDecomposition {A = A} F [] = zeroTriple A
finiteNearTriadDecomposition {A = A} F (item ∷ items)
  with classify F item
... | lowHigh =
  trans
    (cong (λ tail → _+_ A (contribution F item) tail)
      (finiteNearTriadDecomposition F items))
    (headIntoLowHigh A
      (contribution F item)
      (nearLowHigh F items)
      (nearHighLow F items)
      (nearHighHigh F items))
... | highLow =
  trans
    (cong (λ tail → _+_ A (contribution F item) tail)
      (finiteNearTriadDecomposition F items))
    (headIntoHighLow A
      (contribution F item)
      (nearLowHigh F items)
      (nearHighLow F items)
      (nearHighHigh F items))
... | highHigh =
  trans
    (cong (λ tail → _+_ A (contribution F item) tail)
      (finiteNearTriadDecomposition F items))
    (headIntoHighHigh A
      (contribution F item)
      (nearLowHigh F items)
      (nearHighLow F items)
      (nearHighHigh F items))

finiteTriadPartitionLevel : ProofLevel
finiteTriadPartitionLevel = machineChecked
