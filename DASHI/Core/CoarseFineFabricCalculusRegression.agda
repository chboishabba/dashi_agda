module DASHI.Core.CoarseFineFabricCalculusRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Biology.JCoarseFineFabricCalculusAdapterExact as JAdapter
import DASHI.Core.NDimProjectionLossAdapterExact as NDimAdapter
import DASHI.Physics.WaveProjectionLossAdapterExact as WaveAdapter
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Biology.JCoarseFineConsumerReductionBridgeExact as J
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Modular

------------------------------------------------------------------------
-- RED/GREEN REGRESSION CONTRACT
------------------------------------------------------------------------

projectionCollisionSurface :
  ∀ {Fine Coarse Observation : Set} →
  (project : Fine → Coarse) →
  (observe : Fine → Observation) →
  Set
projectionCollisionSurface = Calculus.ProjectionCollision

consumerCannotFactorThroughProjectionSurface :
  ∀ {Fine Coarse Observation : Set}
    {project : Fine → Coarse}
    {observe : Fine → Observation} →
  Calculus.ProjectionCollision project observe →
  (coarseObserve : Coarse → Observation) →
  ((state : Fine) → observe state ≡ coarseObserve (project state)) →
  ⊥
consumerCannotFactorThroughProjectionSurface =
  Calculus.consumerCannotFactorThroughProjection

jCoarseFineProjectionLossAdapterSurface :
  ∀ {Observation : Set}
    {observe : Modular.AbsoluteAddress → Observation} →
  Fibre.FineSensitiveConsumer J.jCoarseFineReopening observe →
  Calculus.ProjectionCollision Modular.forgetFine observe
jCoarseFineProjectionLossAdapterSurface =
  JAdapter.jCoarseFineProjectionLossAdapter

nDimProjectionBoundaryAdapterSurface :
  NDimAdapter.NDimProjectionBoundaryAdapter
nDimProjectionBoundaryAdapterSurface =
  NDimAdapter.nDimProjectionBoundaryAdapter

waveProjectionStatusSurface : WaveAdapter.WaveProjectionStatus
waveProjectionStatusSurface = WaveAdapter.waveProjectionStatus

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
