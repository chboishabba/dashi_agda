module DASHI.Physics.Optics.DiffuserRestrictedStabilityProducerExact where

-- Producer bridge for the existing conditional inverse theorem.
-- The only acceptable restricted-stability budget here is one whose encoder
-- is pointwise the exact same DiffuserForwardModel.encode used by the physical
-- camera weld.  This prevents a numerically convenient surrogate H from
-- silently paying the theorem for a different instrument.

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact as Camera
import DASHI.Physics.Optics.DiffuserNoiseStableRecoveryExact as Stability
import DASHI.Physics.Optics.DiffuserPhysicalForwardWeldExact as Physical

record RestrictedSeparationProducer
    {Scene Sensor Position Depth Pattern Field Intensity : Set}
    (M : Camera.DiffuserForwardModel Scene Sensor Position Depth Pattern)
    (W : Physical.PhysicalDiffuserForwardWeld
      {Scene} {Sensor} {Position} {Depth} {Pattern} {Field} {Intensity} M) : Set₁ where
  field
    budget : Stability.RestrictedInverseBudget Scene Sensor

    sameEncoder :
      (x : Scene) →
      Stability.encoder budget x ≡ Camera.encode M x

    -- The admissible scene family and quantitative restricted lower bound are
    -- carried by budget itself.  They must come from this selected instrument.
    producerAuthority : Set
    producerReceipt : producerAuthority

open RestrictedSeparationProducer public

toRestrictedInverseBudget :
  ∀ {Scene Sensor Position Depth Pattern Field Intensity : Set}
    {M : Camera.DiffuserForwardModel Scene Sensor Position Depth Pattern}
    {W : Physical.PhysicalDiffuserForwardWeld
      {Scene} {Sensor} {Position} {Depth} {Pattern} {Field} {Intensity} M} →
  RestrictedSeparationProducer M W →
  Stability.RestrictedInverseBudget Scene Sensor
toRestrictedInverseBudget P = budget P

-- This module intentionally does not assert RIP, coherence or a singular-value
-- bound generically.  Any such numerical/analytic certificate must populate
-- the restrictedStability field of the same returned budget.
