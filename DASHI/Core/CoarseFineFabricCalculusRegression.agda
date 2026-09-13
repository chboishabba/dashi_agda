module DASHI.Core.CoarseFineFabricCalculusRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus

------------------------------------------------------------------------
-- RED/GREEN REGRESSION CONTRACT
--
-- This regression intentionally names the cross-domain surfaces before the
-- production owner exists.  The first tranche must expose one projection-loss
-- theorem family and three grounded adapter/status surfaces without collapsing
-- static information loss into dynamic noncongruence or promoting 369 as the
-- generic fabric.
------------------------------------------------------------------------

projectionCollisionSurface : Set₁
projectionCollisionSurface = Calculus.ProjectionCollision

consumerCannotFactorThroughProjectionSurface =
  Calculus.consumerCannotFactorThroughProjection

jCoarseFineProjectionLossAdapterSurface =
  Calculus.jCoarseFineProjectionLossAdapter

nDimProjectionBoundaryAdapterSurface =
  Calculus.nDimProjectionBoundaryAdapter

waveProjectionStatusSurface =
  Calculus.waveProjectionStatus

staticNonrecoverabilityIsDynamicNoncongruence : Bool
staticNonrecoverabilityIsDynamicNoncongruence =
  Calculus.staticNonrecoverabilityIsDynamicNoncongruence

staticNonrecoverabilityIsDynamicNoncongruenceIsFalse :
  staticNonrecoverabilityIsDynamicNoncongruence ≡ false
staticNonrecoverabilityIsDynamicNoncongruenceIsFalse = refl

hyperfabric369PromotedAsGenericFabricInThisTranche : Bool
hyperfabric369PromotedAsGenericFabricInThisTranche =
  Calculus.hyperfabric369PromotedAsGenericFabricInThisTranche

hyperfabric369PromotedAsGenericFabricInThisTrancheIsFalse :
  hyperfabric369PromotedAsGenericFabricInThisTranche ≡ false
hyperfabric369PromotedAsGenericFabricInThisTrancheIsFalse = refl
