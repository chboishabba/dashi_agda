module DASHI.Core.ObserverRefinementOrientationCrosswalkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ObserverRefinementCore as Core
import DASHI.Core.ObserverRefinementLatticeExact as Lattice

------------------------------------------------------------------------
-- OBSERVER-REFINEMENT ORIENTATION CROSSWALK
--
-- The two existing Core owners use opposite argument conventions for the same
-- information order:
--
--   Lattice.Refines coarse fine
--     = equality under fine implies equality under coarse
--
--   Core.Refines finer coarser
--     = equality under finer implies equality under coarser
--
-- Therefore the exact translation reverses the two observer arguments.  This
-- module preserves both historical APIs while preventing a third refinement
-- relation from being invented merely to bridge them.
------------------------------------------------------------------------

latticeRefinesToCore :
  ∀ {State Coarse Fine : Set}
    {coarse : State → Coarse}
    {fine : State → Fine} →
  Lattice.Refines coarse fine →
  Core.Refines fine coarse
latticeRefinesToCore refinement = refinement

coreRefinesToLattice :
  ∀ {State Coarse Fine : Set}
    {coarse : State → Coarse}
    {fine : State → Fine} →
  Core.Refines fine coarse →
  Lattice.Refines coarse fine
coreRefinesToLattice refinement = refinement

pairObserversAgreePointwise :
  ∀ {State A B : Set}
    (left : State → A)
    (right : State → B)
    (state : State) →
  Lattice.pairObserver left right state
  ≡ Core.pairObserver left right state
pairObserversAgreePointwise left right state = refl

latticeStrictToCore :
  ∀ {State Coarse Fine : Set}
    {coarse : State → Coarse}
    {fine : State → Fine} →
  Lattice.StrictRefinement coarse fine →
  Core.StrictlyRefines fine coarse
latticeStrictToCore refinement =
  Core.strictlyRefines
    (latticeRefinesToCore (Lattice.refinementLaw refinement))
    (Core.notRefines
      (Lattice.refinementLeft refinement)
      (Lattice.refinementRight refinement)
      (Lattice.refinementCoarseCollision refinement)
      (Lattice.refinementFineSeparates refinement))

coreStrictToLattice :
  ∀ {State Coarse Fine : Set}
    {coarse : State → Coarse}
    {fine : State → Fine} →
  Core.StrictlyRefines fine coarse →
  Lattice.StrictRefinement coarse fine
coreStrictToLattice refinement =
  Lattice.strictRefinement
    (coreRefinesToLattice (Core.refines refinement))
    (Core.leftState (Core.reverseRefinementFails refinement))
    (Core.rightState (Core.reverseRefinementFails refinement))
    (Core.sameLeftObservation (Core.reverseRefinementFails refinement))
    (Core.differentRightObservation (Core.reverseRefinementFails refinement))
