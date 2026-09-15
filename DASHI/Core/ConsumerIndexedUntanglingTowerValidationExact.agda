module DASHI.Core.ConsumerIndexedUntanglingTowerValidationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower

roundTrip :
  ∀ {State n}
    (tower : Tower.UntanglingTower State n)
    (state : State) →
  Tower.decodeTower tower (Tower.encodeTower tower state) ≡ state
roundTrip = Tower.towerRoundTrip

boundary : Tower.ConsumerIndexedUntanglingTowerBoundary
boundary = Tower.canonicalConsumerIndexedUntanglingTowerBoundary
