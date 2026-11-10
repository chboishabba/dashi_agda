module DASHI.Physics.Motors.Circuit36927TwoNodeKCLExact where

------------------------------------------------------------------------
-- Two-edge junction KCL algebra for equal directed branch currents.
-- This closes the elementary series-node cancellation *conditionally*.
-- It does not assert equality of physical branch currents from a
-- catalogue claim; that equality comes from an electrical model.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Resonate369SignedPitchTelescopingExact as Group

module TwoEdgeJunction {A : Set} (G : Group.AngularGroup A) where
  open Group.AngularGroup G

  -- Incoming and outgoing currents have identical chosen orientation
  -- magnitude. The signed node balance is incoming - outgoing.
  nodeBalance : A → A → A
  nodeBalance incoming outgoing = incoming ⊕ neg outgoing

  equalBranchCurrentsGiveKCL : (i : A) →
    nodeBalance i i ≡ zero
  equalBranchCurrentsGiveKCL i = rightInverse i

  -- Reversing the declared external sign convention reverses both
  -- signed contributions; this does not alter node balance.
  equalOppositeOrientationGiveKCL : (i : A) →
    nodeBalance (neg i) (neg i) ≡ zero
  equalOppositeOrientationGiveKCL i = rightInverse (neg i)

  -- A measured or simulated circuit can instantiate these lemmas
  -- only after a same-node, same-time current-equality proof.
