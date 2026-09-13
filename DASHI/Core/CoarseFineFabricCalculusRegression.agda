module DASHI.Core.CoarseFineFabricCalculusRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Biology.JCoarseFineFabricCalculusAdapterExact as JAdapter
import DASHI.Core.NDimProjectionLossAdapterExact as NDimAdapter
import DASHI.Physics.WaveProjectionLossAdapterExact as WaveAdapter

------------------------------------------------------------------------
-- RED/GREEN REGRESSION CONTRACT
--
-- Core remains domain-neutral.  J, NDim, and wave are independently imported
-- manifestations of the shared projection-loss surface.
------------------------------------------------------------------------

projectionCollisionSurface = Calculus.ProjectionCollision

consumerCannotFactorThroughProjectionSurface =
  Calculus.consumerCannotFactorThroughProjection

jCoarseFineProjectionLossAdapterSurface =
  JAdapter.jCoarseFineProjectionLossAdapter

nDimProjectionBoundaryAdapterSurface =
  NDimAdapter.nDimProjectionBoundaryAdapter

waveProjectionStatusSurface =
  WaveAdapter.waveProjectionStatus

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
