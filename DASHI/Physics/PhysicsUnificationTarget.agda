module DASHI.Physics.PhysicsUnificationTarget where

open import DASHI.Physics.RealClosureKit as RK
open import DASHI.Physics.UnifiedClosure as UC

PhysicsGoal : RK.RealClosureKit → Set₂
PhysicsGoal k = UC.PhysicsUnification (RK.toRealStack k)

physicsUnification : (k : RK.RealClosureKit) → Set₂
physicsUnification k = UC.PhysicsUnification (RK.toRealStack k)
