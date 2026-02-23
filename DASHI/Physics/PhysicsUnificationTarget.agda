module DASHI.Physics.PhysicsUnificationTarget where

open import DASHI.Physics.RealClosureKit as RK
open import DASHI.Physics.UnifiedClosure as UC

PhysicsGoal : RK.RealClosureKit → Set₁
PhysicsGoal k = UC.PhysicsUnification (RK.toRealStack k)

physicsUnification : (k : RK.RealClosureKit) → Set₁
physicsUnification k = UC.PhysicsUnification (RK.toRealStack k)

