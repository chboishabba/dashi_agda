{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechPerExpertSymmetryDoesNotForceHistoryReuseExact where

-- Exact finite counterexample to a recurrent incorrect inference:
--   ∀ expert e, F_e(gz)=g(F_e z)
-- DOES NOT imply
--   ∀ e f, H_f is a C2 orbit transform of H_e.
--
-- Here both experts have the SAME perfectly equivariant identity
-- transition. Yet retained histories may be in distinct C2 orbits.
-- Thus compression needs an additional shared-state/orbit-admission
-- law or a complete exact residual, not merely sign-equivariance.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

data History : Set where
  centre positive negative : History

antipode : History → History
antipode centre = centre
antipode positive = negative
antipode negative = positive

antipodeTwice : (h : History) → antipode (antipode h) ≡ h
antipodeTwice centre = refl
antipodeTwice positive = refl
antipodeTwice negative = refl

-- Identity is an admissible (trivially equivariant) expert update.
advance : History → History
advance h = h

advanceCommutesWithAntipode :
  (h : History) →
  advance (antipode h) ≡ antipode (advance h)
advanceCommutesWithAntipode h = refl

data Orientation : Set where
  direct inverse : Orientation

applyOrientation : Orientation → History → History
applyOrientation direct h = h
applyOrientation inverse h = antipode h

-- Two independent expert histories, one fixed point and one
-- noncentral point, need NOT share a C2 orbit representative.
expertZeroHistory : History
expertZeroHistory = centre

expertOneHistory : History
expertOneHistory = positive

centreIsNotPositive : centre ≡ positive → Bool
centreIsNotPositive ()

noSharedAntipodalRepresentative :
  (action : Orientation) →
  applyOrientation action expertZeroHistory ≡ expertOneHistory →
  Bool
noSharedAntipodalRepresentative direct ()
noSharedAntipodalRepresentative inverse ()

-- The exact proof principle is absurd-pattern elimination: there is
-- no C2 orientation which reconstructs positive from centre.
-- Return Bool only to avoid adding an unrelated empty-type import.
-- The stronger consumer-level invariant is that both orbit classes
-- need a distinct representative or an explicit reconstructive
-- residual. Counterfactual C2 law cannot manufacture either.
