module DASHI.Physics.YangMills.BalabanSU2AxisSlabPatchCover where

------------------------------------------------------------------------
-- Exact finite patch geometry discovered by the local-parametrix search.
--
-- On the 2^4 torus, an axis slab fixes three coordinates and leaves one
-- coordinate free.  Thus every slab has shape 2 x 1 x 1 x 1 (up to axis
-- permutation), contains exactly the two sites differing in its free
-- coordinate, and is a proper subset of the sixteen-site torus.
--
-- The theorem below proves the structural part needed by the parametrix lane:
-- every site belongs to exactly one such slab in each of the four orientations.
-- It does not import the numerical remainder estimate and does not promote the
-- finite 2^4 computation to a volume-uniform random-walk theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_×_; _,_)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; Axis4
  ; axis₀
  ; axis₁
  ; axis₂
  ; axis₃
  )

------------------------------------------------------------------------
-- A slab is indexed only by the three fixed coordinates.  The constructor
-- records which coordinate is free.
------------------------------------------------------------------------

data AxisSlab2 : Set where
  slab₀ : Fin 2 → Fin 2 → Fin 2 → AxisSlab2
  slab₁ : Fin 2 → Fin 2 → Fin 2 → AxisSlab2
  slab₂ : Fin 2 → Fin 2 → Fin 2 → AxisSlab2
  slab₃ : Fin 2 → Fin 2 → Fin 2 → AxisSlab2

slabOrientation : AxisSlab2 → Axis4
slabOrientation (slab₀ _ _ _) = axis₀
slabOrientation (slab₁ _ _ _) = axis₁
slabOrientation (slab₂ _ _ _) = axis₂
slabOrientation (slab₃ _ _ _) = axis₃

------------------------------------------------------------------------
-- Membership fixes precisely the coordinates transverse to the free axis.
------------------------------------------------------------------------

InAxisSlab : AxisSlab2 → Cube4 2 → Set
InAxisSlab (slab₀ a₁ a₂ a₃) (cube4 x₀ x₁ x₂ x₃) =
  (x₁ ≡ a₁) × ((x₂ ≡ a₂) × (x₃ ≡ a₃))
InAxisSlab (slab₁ a₀ a₂ a₃) (cube4 x₀ x₁ x₂ x₃) =
  (x₀ ≡ a₀) × ((x₂ ≡ a₂) × (x₃ ≡ a₃))
InAxisSlab (slab₂ a₀ a₁ a₃) (cube4 x₀ x₁ x₂ x₃) =
  (x₀ ≡ a₀) × ((x₁ ≡ a₁) × (x₃ ≡ a₃))
InAxisSlab (slab₃ a₀ a₁ a₂) (cube4 x₀ x₁ x₂ x₃) =
  (x₀ ≡ a₀) × ((x₁ ≡ a₁) × (x₂ ≡ a₂))

------------------------------------------------------------------------
-- The canonical slab through a point in a chosen orientation.
------------------------------------------------------------------------

axisSlabThrough : Axis4 → Cube4 2 → AxisSlab2
axisSlabThrough axis₀ (cube4 x₀ x₁ x₂ x₃) = slab₀ x₁ x₂ x₃
axisSlabThrough axis₁ (cube4 x₀ x₁ x₂ x₃) = slab₁ x₀ x₂ x₃
axisSlabThrough axis₂ (cube4 x₀ x₁ x₂ x₃) = slab₂ x₀ x₁ x₃
axisSlabThrough axis₃ (cube4 x₀ x₁ x₂ x₃) = slab₃ x₀ x₁ x₂

axisSlabThroughOrientation :
  ∀ axis point → slabOrientation (axisSlabThrough axis point) ≡ axis
axisSlabThroughOrientation axis₀ (cube4 x₀ x₁ x₂ x₃) = refl
axisSlabThroughOrientation axis₁ (cube4 x₀ x₁ x₂ x₃) = refl
axisSlabThroughOrientation axis₂ (cube4 x₀ x₁ x₂ x₃) = refl
axisSlabThroughOrientation axis₃ (cube4 x₀ x₁ x₂ x₃) = refl

axisSlabThroughContains :
  ∀ axis point → InAxisSlab (axisSlabThrough axis point) point
axisSlabThroughContains axis₀ (cube4 x₀ x₁ x₂ x₃) =
  refl , (refl , refl)
axisSlabThroughContains axis₁ (cube4 x₀ x₁ x₂ x₃) =
  refl , (refl , refl)
axisSlabThroughContains axis₂ (cube4 x₀ x₁ x₂ x₃) =
  refl , (refl , refl)
axisSlabThroughContains axis₃ (cube4 x₀ x₁ x₂ x₃) =
  refl , (refl , refl)

------------------------------------------------------------------------
-- Orientation evidence is proof relevant.  It lets uniqueness be stated
-- without relying on decidable equality or a Boolean orientation comparison.
------------------------------------------------------------------------

data HasSlabOrientation : AxisSlab2 → Axis4 → Set where
  orientation₀ : ∀ a₁ a₂ a₃ → HasSlabOrientation (slab₀ a₁ a₂ a₃) axis₀
  orientation₁ : ∀ a₀ a₂ a₃ → HasSlabOrientation (slab₁ a₀ a₂ a₃) axis₁
  orientation₂ : ∀ a₀ a₁ a₃ → HasSlabOrientation (slab₂ a₀ a₁ a₃) axis₂
  orientation₃ : ∀ a₀ a₁ a₂ → HasSlabOrientation (slab₃ a₀ a₁ a₂) axis₃

axisSlabThroughHasOrientation :
  ∀ axis point → HasSlabOrientation (axisSlabThrough axis point) axis
axisSlabThroughHasOrientation axis₀ (cube4 x₀ x₁ x₂ x₃) =
  orientation₀ x₁ x₂ x₃
axisSlabThroughHasOrientation axis₁ (cube4 x₀ x₁ x₂ x₃) =
  orientation₁ x₀ x₂ x₃
axisSlabThroughHasOrientation axis₂ (cube4 x₀ x₁ x₂ x₃) =
  orientation₂ x₀ x₁ x₃
axisSlabThroughHasOrientation axis₃ (cube4 x₀ x₁ x₂ x₃) =
  orientation₃ x₀ x₁ x₂

------------------------------------------------------------------------
-- Uniqueness: among slabs with a fixed orientation, membership determines all
-- three fixed coordinates, hence determines the slab itself.
------------------------------------------------------------------------

axisSlabThroughUnique :
  ∀ slab point axis →
  HasSlabOrientation slab axis →
  InAxisSlab slab point →
  slab ≡ axisSlabThrough axis point
axisSlabThroughUnique
  (slab₀ a₁ a₂ a₃) (cube4 x₀ .a₁ .a₂ .a₃) axis₀
  (orientation₀ .a₁ .a₂ .a₃)
  (refl , (refl , refl)) = refl
axisSlabThroughUnique
  (slab₁ a₀ a₂ a₃) (cube4 .a₀ x₁ .a₂ .a₃) axis₁
  (orientation₁ .a₀ .a₂ .a₃)
  (refl , (refl , refl)) = refl
axisSlabThroughUnique
  (slab₂ a₀ a₁ a₃) (cube4 .a₀ .a₁ x₂ .a₃) axis₂
  (orientation₂ .a₀ .a₁ .a₃)
  (refl , (refl , refl)) = refl
axisSlabThroughUnique
  (slab₃ a₀ a₁ a₂) (cube4 .a₀ .a₁ .a₂ x₃) axis₃
  (orientation₃ .a₀ .a₁ .a₂)
  (refl , (refl , refl)) = refl

------------------------------------------------------------------------
-- The finite cover theorem, packaged without any analytic estimate.
------------------------------------------------------------------------

record UniqueAxisSlabCover (point : Cube4 2) : Set where
  field
    coveringSlab : Axis4 → AxisSlab2
    coveringOrientation :
      ∀ axis → HasSlabOrientation (coveringSlab axis) axis
    coveringMembership :
      ∀ axis → InAxisSlab (coveringSlab axis) point
    uniqueAtOrientation :
      ∀ slab axis →
      HasSlabOrientation slab axis →
      InAxisSlab slab point →
      slab ≡ coveringSlab axis

open UniqueAxisSlabCover public

axisSlabCover2 : ∀ point → UniqueAxisSlabCover point
axisSlabCover2 point = record
  { coveringSlab = λ axis → axisSlabThrough axis point
  ; coveringOrientation = λ axis → axisSlabThroughHasOrientation axis point
  ; coveringMembership = λ axis → axisSlabThroughContains axis point
  ; uniqueAtOrientation = λ slab axis orientation membership →
      axisSlabThroughUnique slab point axis orientation membership
  }
