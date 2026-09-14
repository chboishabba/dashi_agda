module DASHI.Cognition.PNF.CoarseFineStaticDynamicBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (proj₂)

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Cognition.PNF.TerminalisationDefectRegression as Existing
import DASHI.Cognition.PNF.CoarseFineStaticDynamicBridgeExact as Bridge

------------------------------------------------------------------------
-- RED/GREEN contract: one existing residual fibre must support both a static
-- hidden-coordinate collision and a dynamic future-divergence witness, while
-- preserving their logical distinction.
------------------------------------------------------------------------

residualStaticCollisionSurface :
  Calculus.ProjectionCollision Existing.residualProjection proj₂
residualStaticCollisionSurface = Bridge.residualStaticCollision

residualDynamicDefectSurface :
  Dynamic.TerminalisationDefect
    Existing.residualSystem
    Existing.residualProjection
residualDynamicDefectSurface = Bridge.residualDynamicDefect

residualDynamicSafetyRefutedSurface :
  Dynamic.DynamicConsumerSafety
    Existing.residualSystem
    Existing.residualProjection →
  ⊥
residualDynamicSafetyRefutedSurface = Bridge.residualDynamicSafetyRefuted

staticCollisionAutomaticallyCreatesDynamicDefect : Bool
staticCollisionAutomaticallyCreatesDynamicDefect =
  Bridge.StaticDynamicBridgeBoundary.staticCollisionAutomaticallyCreatesDynamicDefect
    Bridge.canonicalStaticDynamicBridgeBoundary

staticCollisionAutomaticallyCreatesDynamicDefectIsFalse :
  staticCollisionAutomaticallyCreatesDynamicDefect ≡ false
staticCollisionAutomaticallyCreatesDynamicDefectIsFalse = refl

dynamicDefectAutomaticallyCreatesStaticCollision : Bool
dynamicDefectAutomaticallyCreatesStaticCollision =
  Bridge.StaticDynamicBridgeBoundary.dynamicDefectAutomaticallyCreatesStaticCollision
    Bridge.canonicalStaticDynamicBridgeBoundary

dynamicDefectAutomaticallyCreatesStaticCollisionIsFalse :
  dynamicDefectAutomaticallyCreatesStaticCollision ≡ false
dynamicDefectAutomaticallyCreatesStaticCollisionIsFalse = refl
