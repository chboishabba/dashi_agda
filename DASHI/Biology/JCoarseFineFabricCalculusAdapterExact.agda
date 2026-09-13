module DASHI.Biology.JCoarseFineFabricCalculusAdapterExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Biology.JCoarseFineConsumerReductionBridgeExact as J
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Modular

------------------------------------------------------------------------
-- JCOARSE / JFINE -> GENERIC PROJECTION COLLISION
--
-- This adapter does not add a new J witness.  It translates any existing
-- FineSensitiveConsumer over the canonical J reopening into the weaker generic
-- projection-collision surface.
------------------------------------------------------------------------

jCoarseFineProjectionLossAdapter :
  ∀ {Observation : Set}
    {observe : Modular.AbsoluteAddress → Observation} →
  Fibre.FineSensitiveConsumer J.jCoarseFineReopening observe →
  Calculus.ProjectionCollision Modular.forgetFine observe
jCoarseFineProjectionLossAdapter witness =
  Calculus.projectionCollision
    (Fibre.left witness)
    (Fibre.right witness)
    (Fibre.sameCoarse witness)
    (Fibre.consumerSeparates witness)

jCoarseFineGenericNonFactorability :
  ∀ {Observation : Set}
    {observe : Modular.AbsoluteAddress → Observation} →
  Fibre.FineSensitiveConsumer J.jCoarseFineReopening observe →
  (coarseObserve : Modular.CoarseAddress → Observation) →
  ((state : Modular.AbsoluteAddress) →
    observe state ≡ coarseObserve (Modular.forgetFine state)) →
  ⊥
jCoarseFineGenericNonFactorability witness =
  Calculus.consumerCannotFactorThroughProjection
    (jCoarseFineProjectionLossAdapter witness)
