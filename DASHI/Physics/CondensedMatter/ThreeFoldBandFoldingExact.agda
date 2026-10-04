module DASHI.Physics.CondensedMatter.ThreeFoldBandFoldingExact where

------------------------------------------------------------------------
-- THREE-FOLD BAND-FOLDING SURFACE
--
-- The Fe5GeTe2 source reports sqrt(3) x sqrt(3) R30-degree charge order.
-- This module contributes only the exact finite quotient shape needed for
-- three folded momentum representatives.
--
-- It does NOT claim that this finite carrier proves the crystallographic
-- sqrt(3) x sqrt(3) R30-degree geometry.  A physical instantiation must provide
-- the actual reciprocal-lattice/supercell map and prove that it realizes this
-- quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)

Injective : {A B : Set} -> (A -> B) -> Set
Injective f = ∀ {x y} -> f x ≡ f y -> x ≡ y

record ThreeFoldPresentation (Momentum FoldedMomentum : Set) : Set₁ where
  constructor three-fold-presentation
  field
    first second third : Momentum
    fold : Momentum -> FoldedMomentum
    firstSecondDistinct : first ≡ second -> ⊥
    firstThirdDistinct : first ≡ third -> ⊥
    secondThirdDistinct : second ≡ third -> ⊥
    firstSecondFoldTogether : fold first ≡ fold second
    firstThirdFoldTogether : fold first ≡ fold third

open ThreeFoldPresentation public

threeFoldPresentationRefutesInjectiveFold :
  {Momentum FoldedMomentum : Set} ->
  (presentation : ThreeFoldPresentation Momentum FoldedMomentum) ->
  Injective (fold presentation) ->
  ⊥
threeFoldPresentationRefutesInjectiveFold presentation injective =
  firstSecondDistinct presentation
    (injective (firstSecondFoldTogether presentation))

data OneFoldedPoint : Set where
  foldedPoint : OneFoldedPoint

canonicalThreeLaneFold :
  Fin 3 -> OneFoldedPoint
canonicalThreeLaneFold _ = foldedPoint

zeroNotOne : (zero {2} ≡ suc zero) -> ⊥
zeroNotOne ()

zeroNotTwo : (zero {2} ≡ suc (suc zero)) -> ⊥
zeroNotTwo ()

oneNotTwo : (suc zero ≡ suc (suc zero) : Fin 3) -> ⊥
oneNotTwo ()

canonicalThreeFoldPresentation :
  ThreeFoldPresentation (Fin 3) OneFoldedPoint
canonicalThreeFoldPresentation =
  three-fold-presentation
    zero
    (suc zero)
    (suc (suc zero))
    canonicalThreeLaneFold
    zeroNotOne
    zeroNotTwo
    oneNotTwo
    refl
    refl

record ThreeFoldPhysicalBoundary : Set where
  constructor three-fold-physical-boundary
  field
    exactThreeToOneFiniteSurfaceAvailable : Bool
    noninjectivityOfFiniteFoldProved : Bool
    sqrt3R30CrystallographyDerivedFromFiniteSurface : Bool
    physicalReciprocalLatticeMapStillRequired : Bool

canonicalThreeFoldPhysicalBoundary : ThreeFoldPhysicalBoundary
canonicalThreeFoldPhysicalBoundary =
  three-fold-physical-boundary
    true true
    false true
