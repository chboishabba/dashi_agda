module DASHI.Core.ObserverRefinementOrientationCrosswalkRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ObserverRefinementCore as Core
import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Core.ObserverRefinementOrientationCrosswalkExact as Crosswalk

record State : Set where
  constructor state
  field
    coarse : Bool
    fine : Bool
open State public

coarseObserver : State → Bool
coarseObserver = coarse

fineObserver : State → Bool
fineObserver = fine

pairObserversAgreePointwise :
  (x : State) →
  Lattice.pairObserver coarseObserver fineObserver x
  ≡ Core.pairObserver coarseObserver fineObserver x
pairObserversAgreePointwise = Crosswalk.pairObserversAgreePointwise

refinementOrientationRoundTrip :
  Lattice.Refines coarseObserver (Lattice.pairObserver coarseObserver fineObserver)
refinementOrientationRoundTrip =
  Crosswalk.coreRefinesToLattice
    (Crosswalk.latticeRefinesToCore
      (Lattice.pairRefinesLeft coarseObserver fineObserver))

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

strictLattice :
  Lattice.StrictRefinement
    coarseObserver
    (Lattice.pairObserver coarseObserver fineObserver)
strictLattice =
  Lattice.strictPairRefinement
    coarseObserver
    fineObserver
    (state false true)
    (state false false)
    refl
    trueNotFalse

strictCore :
  Core.StrictlyRefines
    (Core.pairObserver coarseObserver fineObserver)
    coarseObserver
strictCore = Crosswalk.latticeStrictToCore strictLattice

strictRoundTrip :
  Lattice.StrictRefinement
    coarseObserver
    (Lattice.pairObserver coarseObserver fineObserver)
strictRoundTrip = Crosswalk.coreStrictToLattice strictCore
