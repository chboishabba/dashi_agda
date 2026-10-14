module DASHI.Core.TypedDependencyCoreUniverseRegression where

open import Agda.Builtin.String using (String)
open import Data.Unit using (⊤)

import DASHI.Core.TypedDependencyCore as Dependency

data TestAction : Set where
  testAction : TestAction

data SmallState : Set where
  smallState : SmallState

smallSystem : Dependency.DependentActionSystem {State = SmallState} TestAction
smallSystem = record
  { Precondition = λ _ _ → ⊤
  ; Postcondition = λ _ _ _ → ⊤
  ; actionLabel = λ _ → "small"
  }

-- `Set` itself is a Set₁-valued state carrier.  This pins the intended
-- universe-polymorphic use rather than merely repairing the Set₀ case.
largeSystem : Dependency.DependentActionSystem {State = Set} TestAction
largeSystem = record
  { Precondition = λ _ _ → ⊤
  ; Postcondition = λ _ _ _ → ⊤
  ; actionLabel = λ _ → "large"
  }
