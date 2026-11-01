module DASHI.Core.RequiredObserverAxisJoinCanonicalPairRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join

jointAxisIsCanonicalPairObserver :
  ∀ {State A B : Set}
    (left : State → A)
    (right : State → B)
    (state : State) →
  Join.jointAxis left right state
  ≡ Observer.pairObserver left right state
jointAxisIsCanonicalPairObserver = Join.jointAxisIsCanonicalPairObserver
