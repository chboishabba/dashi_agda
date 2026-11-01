module DASHI.Semantics.SIOObserverRefinementLatticeAdapterExact where

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

import DASHI.Core.ObserverRefinementCore as Core
import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Core.ObserverRefinementOrientationCrosswalkExact as Crosswalk
import DASHI.Semantics.SIOSemanticSurfaceBridge as SIO

------------------------------------------------------------------------
-- SIO -> CANONICAL OBSERVER REFINEMENT LATTICE
--
-- SIO keeps its historical ObserverRefinementCore API.  This adapter does not
-- rewrite that API; it translates SIO's already-proved strict pair refinement
-- into the canonical lattice orientation used by newer #902 consumers.
------------------------------------------------------------------------

sioPairedObserverCanonicalStrictRefinements :
  ∀ {X A B : Set}
    {OA : SIO.SIOAttributeObserver X A}
    {OB : SIO.SIOAttributeObserver X B} →
  Core.CrossCollision OA OB →
  Lattice.StrictRefinement OA (Core.pairObserver OA OB) ×
  Lattice.StrictRefinement OB (Core.pairObserver OA OB)
sioPairedObserverCanonicalStrictRefinements witness =
  let refinements = SIO.sioPairedObserverStrictlyRefinesBoth witness
  in Crosswalk.coreStrictToLattice (proj₁ refinements)
     , Crosswalk.coreStrictToLattice (proj₂ refinements)
