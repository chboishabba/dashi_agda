module DASHI.Core.ProvenanceQuotientDynamics where

open import Data.Empty using (⊥)

import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Reopenability and dynamic safety are independent obligations.
--
-- A quotient may reconstruct the fine state exactly from its receipt while the
-- coarse surface alone remains unsafe for a consumer whose future transitions
-- depend on information stored in that receipt.
------------------------------------------------------------------------

record DynamicallySafeProvenanceProjection
    (core : Fibre.FibreRestrictionCore)
    (Action : Set)
    (system :
      Dependency.DependentActionSystem (Fibre.Carrier core) Action) : Set₁ where
  constructor dynamicallySafeProvenanceProjection
  field
    quotient : Quotient.ProvenanceBearingQuotient core
    consumerSafety :
      Dynamic.DynamicConsumerSafety system (Fibre.project core)

open DynamicallySafeProvenanceProjection public

record ReopenableButDynamicallyUnsafe
    (core : Fibre.FibreRestrictionCore)
    (Action : Set)
    (system :
      Dependency.DependentActionSystem (Fibre.Carrier core) Action) : Set₁ where
  constructor reopenableButDynamicallyUnsafe
  field
    quotient : Quotient.ProvenanceBearingQuotient core
    defect : Dynamic.TerminalisationDefect system (Fibre.project core)

open ReopenableButDynamicallyUnsafe public

unsafeProjectionCannotCarrySafety :
  ∀ {core Action system} →
  ReopenableButDynamicallyUnsafe core Action system →
  Dynamic.DynamicConsumerSafety system (Fibre.project core) →
  ⊥
unsafeProjectionCannotCarrySafety unsafe safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    (defect unsafe)
