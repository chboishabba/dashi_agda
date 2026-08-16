module DASHI.Physics.YangMills.BalabanClayT4RegularGridOuterAxisExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The generated 4^4 Brillouin partition removes exactly the 2^4 all-inner
-- cells.  Hence every one of the 240 regular cells has at least one coordinate
-- in an outer interval [1/2,1] or [-1,-1/2].  This finite theorem is useful for
-- the one-loop denominator: after a single outer-axis sine-half lower bound is
-- proved, strict positivity of hat{k}^2 follows uniformly on every regular box.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid

data OuterAxisWitness (cell : Grid.GridCell4) : Set where
  outer0 : Grid.isInner (Grid.c0 cell) ≡ false → OuterAxisWitness cell
  outer1 : Grid.isInner (Grid.c1 cell) ≡ false → OuterAxisWitness cell
  outer2 : Grid.isInner (Grid.c2 cell) ≡ false → OuterAxisWitness cell
  outer3 : Grid.isInner (Grid.c3 cell) ≡ false → OuterAxisWitness cell

regularCellHasOuterAxis :
  ∀ cell → Grid.allInner cell ≡ false → OuterAxisWitness cell
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeOuter b c d) regular = outer0 refl
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveOuter b c d) regular = outer0 refl
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter c d) regular = outer1 refl
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter c d) regular = outer1 refl
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter c d) regular = outer1 refl
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter c d) regular = outer1 refl
regularCellHasOuterAxis
  (Grid.gridCell4 a b Grid.negativeOuter d) regular = outer2 refl
regularCellHasOuterAxis
  (Grid.gridCell4 a b Grid.positiveOuter d) regular = outer2 refl
regularCellHasOuterAxis
  (Grid.gridCell4 a b c Grid.negativeOuter) regular = outer3 refl
regularCellHasOuterAxis
  (Grid.gridCell4 a b c Grid.positiveOuter) regular = outer3 refl
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) ()
regularCellHasOuterAxis
  (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) ()

regularOuterAxisGeometryLevel : ProofLevel
regularOuterAxisGeometryLevel = machineChecked
