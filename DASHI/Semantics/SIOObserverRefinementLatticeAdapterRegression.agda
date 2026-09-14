module DASHI.Semantics.SIOObserverRefinementLatticeAdapterRegression where

open import DASHI.Core.Prelude
open import Data.Product using (_×_)

import DASHI.Core.ObserverRefinementCore as Core
import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Semantics.SIOSemanticSurfaceBridge as SIO
import DASHI.Semantics.SIOObserverRefinementLatticeAdapterExact as Adapter

sioCrossCollisionYieldsCanonicalStrictRefinements :
  ∀ {X A B : Set}
    {OA : SIO.SIOAttributeObserver X A}
    {OB : SIO.SIOAttributeObserver X B} →
  Core.CrossCollision OA OB →
  Lattice.StrictRefinement OA (Core.pairObserver OA OB) ×
  Lattice.StrictRefinement OB (Core.pairObserver OA OB)
sioCrossCollisionYieldsCanonicalStrictRefinements =
  Adapter.sioPairedObserverCanonicalStrictRefinements
