{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVoyagerImaginaryC3DimensionBidiExact where

-- FINITE MATHEMATICAL BRIDGE: ORIENTED 2-PLANE QUARTER TURN vs
-- THREE-STATE C3 ACTION.
--
-- The complex imaginary unit can be realised on an oriented real 2-plane
-- by J(x,y)=(-y,x); this is one complex dimension but TWO real dimensions,
-- not an extra real spatial coordinate.  Existing real-pair ComplexPair,
-- multiplication, and imaginaryUnit ownership is in
-- DASHI.Analysis.ConcreteComplex.  This module only proves a finite
-- signed-axis restriction of J and its sharp C3 incompatibility.
--
-- The 3-cycle and 4-cycle do not become the same action merely because
-- both describe rotations. C3 is still useful for *ternary* gauge-chart
-- symmetry if a selected Wilson theory supplies an action-preserving map.
-- Scientific/standard mathematical authorship is not claimed for these
-- elementary finite group facts.
--
-- No Wick analytic continuation, 5D KK metric, or 4D quantum YM follows.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

data SignedAxis2 : Set where
  positiveX : SignedAxis2
  positiveY : SignedAxis2
  negativeX : SignedAxis2
  negativeY : SignedAxis2

-- This rotates an oriented positive Euclidean real plane by +90 degrees.
quarterTurn : SignedAxis2 → SignedAxis2
quarterTurn positiveX = positiveY
quarterTurn positiveY = negativeX
quarterTurn negativeX = negativeY
quarterTurn negativeY = positiveX

axisNegation : SignedAxis2 → SignedAxis2
axisNegation positiveX = negativeX
axisNegation positiveY = negativeY
axisNegation negativeX = positiveX
axisNegation negativeY = positiveY

quarterTurnSquaredIsNegation :
  ∀ axis → quarterTurn (quarterTurn axis) ≡ axisNegation axis
quarterTurnSquaredIsNegation positiveX = refl
quarterTurnSquaredIsNegation positiveY = refl
quarterTurnSquaredIsNegation negativeX = refl
quarterTurnSquaredIsNegation negativeY = refl

negationSquaredIsIdentity :
  ∀ axis → axisNegation (axisNegation axis) ≡ axis
negationSquaredIsIdentity positiveX = refl
negationSquaredIsIdentity positiveY = refl
negationSquaredIsIdentity negativeX = refl
negationSquaredIsIdentity negativeY = refl

quarterTurnFourthIsIdentity :
  ∀ axis →
  quarterTurn
    (quarterTurn (quarterTurn (quarterTurn axis))) ≡ axis
quarterTurnFourthIsIdentity positiveX = refl
quarterTurnFourthIsIdentity positiveY = refl
quarterTurnFourthIsIdentity negativeX = refl
quarterTurnFourthIsIdentity negativeY = refl

quarterTurnIsNotIdentityAtPositiveX :
  quarterTurn positiveX ≡ positiveX → ⊥
quarterTurnIsNotIdentityAtPositiveX ()

-- Exact C3: order three, distinct from the signed two-plane quarter-turn.
data TritPosition : Set where
  phase0 : TritPosition
  phase1 : TritPosition
  phase2 : TritPosition

rotateC3 : TritPosition → TritPosition
rotateC3 phase0 = phase1
rotateC3 phase1 = phase2
rotateC3 phase2 = phase0

c3CubedIsIdentity :
  ∀ t → rotateC3 (rotateC3 (rotateC3 t)) ≡ t
c3CubedIsIdentity phase0 = refl
c3CubedIsIdentity phase1 = refl
c3CubedIsIdentity phase2 = refl

quarterTurnCubedHasNoFixedAxis :
  ∀ axis →
  quarterTurn (quarterTurn (quarterTurn axis)) ≡ axis → ⊥
quarterTurnCubedHasNoFixedAxis positiveX ()
quarterTurnCubedHasNoFixedAxis positiveY ()
quarterTurnCubedHasNoFixedAxis negativeX ()
quarterTurnCubedHasNoFixedAxis negativeY ()

-- A C3 equivariant map to *this* four-state free quarter-turn orbit
-- cannot exist. This does NOT prohibit C3 as an action on a full
-- real plane; that continuous representation has a fixed origin and
-- rotates by 120 degrees, not by this 90-degree action.
--
-- Restrict to the chosen phase0 orbit.  The three provided intertwining
-- equations rewrite quarter^3(f phase0) into f phase0, contradicting
-- the free quarter-turn action.
noC3ToQuarterTurnIntertwiner :
  (f : TritPosition → SignedAxis2) →
  ((t : TritPosition) →
    f (rotateC3 t) ≡ quarterTurn (f t)) → ⊥
noC3ToQuarterTurnIntertwiner f intertwines =
  quarterTurnCubedHasNoFixedAxis (f phase0)
    (trans
      (cong (λ axis → quarterTurn (quarterTurn axis))
        (sym (intertwines phase0)))
      (trans
        (cong quarterTurn (sym (intertwines phase1)))
        (sym (intertwines phase2))))

-- Cross-domain interpretation:
-- * A phase axis counts directions, not extra coordinates.
-- * SO(2) (continuous plane rotations) is not identical with C3.
-- * SU(2)->SO(3) requires Spin double-cover and kernel witnesses.
-- * SO(2) lattice gauge = U(1), not SO(3) physical spatial rotation.
-- * Euclidean/Lorentzian metric signature and a physical fifth
--   coordinate require their own selected physical metric/action.
