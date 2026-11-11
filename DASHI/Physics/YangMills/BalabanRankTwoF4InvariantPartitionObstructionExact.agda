module DASHI.Physics.YangMills.BalabanRankTwoF4InvariantPartitionObstructionExact where

-- Original DASHI finite action-theoretic obstruction.
-- Reuses the ORIGINAL Round56 generated hypercubic path theorem.
-- A rank-two 96-cell W(B4) orbit cannot map surjectively and
-- equivariantly onto two separately labelled invariant target copies,
-- even when the total target count is also 96 = 2 * 48.
--
-- This is a group-set / orbit-partition obstruction, not a no-go for
-- arbitrary F3-linear maps, E6-folded actions, or D4 triality twists.
-- The matching explicit standard F4 root-action enumeration is in
-- scripts/check_round56_rank2_f4_two_copies_action.py.
--
-- Original F4 derivation/finite folding is on separate PR #1106:
--   DASHI.Reasoning.AlbertF4FiniteWeylMaxCutExact
-- Those files are NOT imported from this independent PR #1479 branch.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action

-- A source colour preserved by ALL actual hypercubic generators remains
-- preserved along the finite generated path already proved in Round56.
colourPreservedAlongPath :
  (colour : Grid.GridCell4 → Bool) →
  (invariant : (g : Action.HypercubicGenerator)
               (c : Grid.GridCell4) →
               colour (Action.act g c) ≡ colour c) →
  {a b : Grid.GridCell4} →
  Action.HypercubicPath a b →
  colour a ≡ colour b
colourPreservedAlongPath colour invariant Action.pathRefl = refl
colourPreservedAlongPath colour invariant (Action.pathStep g c) =
  sym (invariant g c)
colourPreservedAlongPath colour invariant (Action.pathTrans first second) =
  trans (colourPreservedAlongPath colour invariant first)
        (colourPreservedAlongPath colour invariant second)

-- IMPORTANT: only the 96 CELL rank-two orbit, not the full 256-cell
-- hypercube and not the 240 union of all four non-infrared orbits.
rankTwoPathToRepresentative :
  (c : Grid.GridCell4) →
  Orbit.orbitClass c ≡ Orbit.twoOuter →
  Action.HypercubicPath c Orbit.twoOuterRepresentative
rankTwoPathToRepresentative c rankTwo =
  Action.pathTargetCong (Action.cellPathToOrbitRepresentative c)
    (cong Action.representative rankTwo)

-- Any two actual rank-two grid cells have the same invariant colour.
rankTwoInvariantColourConstant :
  (colour : Grid.GridCell4 → Bool) →
  (invariant : (g : Action.HypercubicGenerator)
               (c : Grid.GridCell4) →
               colour (Action.act g c) ≡ colour c) →
  (a b : Grid.GridCell4) →
  Orbit.orbitClass a ≡ Orbit.twoOuter →
  Orbit.orbitClass b ≡ Orbit.twoOuter →
  colour a ≡ colour b
rankTwoInvariantColourConstant colour invariant a b aRank bRank =
  trans
    (colourPreservedAlongPath colour invariant
      (rankTwoPathToRepresentative a aRank))
    (sym (colourPreservedAlongPath colour invariant
      (rankTwoPathToRepresentative b bRank)))

-- A target with a two-colour label stable under every selected B4 actor
-- cannot receive an equivariant map hitting both labels from the one
-- actual B4 rank-two source orbit. This is the *precise* 96=2*48
-- no-go, independently of a choice of root coordinate representation.
rankTwoCannotHitTwoInvariantTargetComponents :
  (Target : Set) →
  (targetAct : Action.HypercubicGenerator → Target → Target) →
  (toTarget : Grid.GridCell4 → Target) →
  (tag : Target → Bool) →
  (commutes : (g : Action.HypercubicGenerator)
              (c : Grid.GridCell4) →
              toTarget (Action.act g c) ≡ targetAct g (toTarget c)) →
  (tagInvariant : (g : Action.HypercubicGenerator)
                  (y : Target) → tag (targetAct g y) ≡ tag y) →
  (a b : Grid.GridCell4) →
  (aRank : Orbit.orbitClass a ≡ Orbit.twoOuter) →
  (bRank : Orbit.orbitClass b ≡ Orbit.twoOuter) →
  (differentTag : tag (toTarget a) ≡ tag (toTarget b) → ⊥) →
  ⊥
rankTwoCannotHitTwoInvariantTargetComponents Target targetAct toTarget
  tag commutes tagInvariant a b aRank bRank differentTag =
  differentTag
    (rankTwoInvariantColourConstant
      (λ c → tag (toTarget c))
      (λ g c → trans (cong tag (commutes g c))
                       (tagInvariant g (toTarget c)))
      a b aRank bRank)

-- The conclusion is about the *selected* W(B4) source action:
-- a W(D4) restriction is no longer transitive on all 96 rank-two cells,
-- so this particular proof does not purport to be a W(D4) theorem.
-- The script separately checks W(D4) with its actual two 48-orbit
-- partition and traces, again for only the standard coordinate action.
