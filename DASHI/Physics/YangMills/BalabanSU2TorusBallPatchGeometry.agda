module DASHI.Physics.YangMills.BalabanSU2TorusBallPatchGeometry where

------------------------------------------------------------------------
-- Exact patch geometry behind the improved finite parametrix search.
--
-- On the 2^4 torus every coordinate is a bit.  The torus L1 distance is the
-- number of coordinates that differ, so:
--
--   distance <= 3  iff at least one coordinate agrees;
--   distance <= 2  iff at least two coordinates agree.
--
-- We encode those predicates directly, without a numerical distance oracle.
-- The antipode flips all four coordinates, giving an explicit point outside
-- each radius-two and radius-three ball.  Thus these translated balls cover the
-- torus while each individual patch is still proper.  No analytic remainder
-- bound is imported here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Agda.Builtin.Sigma using (Σ) renaming (_,_ to _,Σ_)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; x₀
  ; x₁
  ; x₂
  ; x₃
  )

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- The fixed-point-free coordinate flip on Fin 2.
------------------------------------------------------------------------

flip2 : Fin 2 → Fin 2
flip2 zero = suc zero
flip2 (suc zero) = zero

flip2NoFixedPoint : ∀ coordinate → flip2 coordinate ≢ coordinate
flip2NoFixedPoint zero ()
flip2NoFixedPoint (suc zero) ()

antipode2 : Cube4 2 → Cube4 2
antipode2 point =
  cube4
    (flip2 (x₀ point))
    (flip2 (x₁ point))
    (flip2 (x₂ point))
    (flip2 (x₃ point))

------------------------------------------------------------------------
-- Radius-three and radius-two membership, written as exact coordinate logic.
------------------------------------------------------------------------

InRadiusThree : Cube4 2 → Cube4 2 → Set
InRadiusThree center point =
  (x₀ center ≡ x₀ point) ⊎
  ((x₁ center ≡ x₁ point) ⊎
   ((x₂ center ≡ x₂ point) ⊎
    (x₃ center ≡ x₃ point)))

InRadiusTwo : Cube4 2 → Cube4 2 → Set
InRadiusTwo center point =
  ((x₀ center ≡ x₀ point) × (x₁ center ≡ x₁ point)) ⊎
  (((x₀ center ≡ x₀ point) × (x₂ center ≡ x₂ point)) ⊎
   (((x₀ center ≡ x₀ point) × (x₃ center ≡ x₃ point)) ⊎
    (((x₁ center ≡ x₁ point) × (x₂ center ≡ x₂ point)) ⊎
     (((x₁ center ≡ x₁ point) × (x₃ center ≡ x₃ point)) ⊎
      ((x₂ center ≡ x₂ point) × (x₃ center ≡ x₃ point))))))

radiusThreeContainsCenter : ∀ center → InRadiusThree center center
radiusThreeContainsCenter center = inj₁ refl

radiusTwoContainsCenter : ∀ center → InRadiusTwo center center
radiusTwoContainsCenter center = inj₁ (refl , refl)

radiusTwoContainedInRadiusThree :
  ∀ {center point} → InRadiusTwo center point → InRadiusThree center point
radiusTwoContainedInRadiusThree (inj₁ (equal₀ , equal₁)) =
  inj₁ equal₀
radiusTwoContainedInRadiusThree (inj₂ (inj₁ (equal₀ , equal₂))) =
  inj₁ equal₀
radiusTwoContainedInRadiusThree
  (inj₂ (inj₂ (inj₁ (equal₀ , equal₃)))) =
  inj₁ equal₀
radiusTwoContainedInRadiusThree
  (inj₂ (inj₂ (inj₂ (inj₁ (equal₁ , equal₂))))) =
  inj₂ (inj₁ equal₁)
radiusTwoContainedInRadiusThree
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (equal₁ , equal₃)))))) =
  inj₂ (inj₁ equal₁)
radiusTwoContainedInRadiusThree
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (equal₂ , equal₃)))))) =
  inj₂ (inj₂ (inj₁ equal₂))

------------------------------------------------------------------------
-- The antipode is a constructive properness witness for both patch radii.
------------------------------------------------------------------------

radiusThreeExcludesAntipode :
  ∀ center → InRadiusThree center (antipode2 center) → ⊥
radiusThreeExcludesAntipode center (inj₁ equal₀) =
  flip2NoFixedPoint (x₀ center) (sym equal₀)
radiusThreeExcludesAntipode center (inj₂ (inj₁ equal₁)) =
  flip2NoFixedPoint (x₁ center) (sym equal₁)
radiusThreeExcludesAntipode center (inj₂ (inj₂ (inj₁ equal₂))) =
  flip2NoFixedPoint (x₂ center) (sym equal₂)
radiusThreeExcludesAntipode center (inj₂ (inj₂ (inj₂ equal₃))) =
  flip2NoFixedPoint (x₃ center) (sym equal₃)

radiusTwoExcludesAntipode :
  ∀ center → InRadiusTwo center (antipode2 center) → ⊥
radiusTwoExcludesAntipode center membership =
  radiusThreeExcludesAntipode center
    (radiusTwoContainedInRadiusThree membership)

radiusThreeProperWitness :
  ∀ center → Σ (Cube4 2) (λ point → InRadiusThree center point → ⊥)
radiusThreeProperWitness center =
  antipode2 center ,Σ radiusThreeExcludesAntipode center

radiusTwoProperWitness :
  ∀ center → Σ (Cube4 2) (λ point → InRadiusTwo center point → ⊥)
radiusTwoProperWitness center =
  antipode2 center ,Σ radiusTwoExcludesAntipode center

------------------------------------------------------------------------
-- Translated cover: every point is covered by the ball centred at that point.
------------------------------------------------------------------------

radiusThreeTranslatedCover :
  ∀ point → Σ (Cube4 2) (λ center → InRadiusThree center point)
radiusThreeTranslatedCover point =
  point ,Σ radiusThreeContainsCenter point

radiusTwoTranslatedCover :
  ∀ point → Σ (Cube4 2) (λ center → InRadiusTwo center point)
radiusTwoTranslatedCover point =
  point ,Σ radiusTwoContainsCenter point
