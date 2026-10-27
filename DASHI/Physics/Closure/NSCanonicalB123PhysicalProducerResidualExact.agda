{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB123PhysicalProducerResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES B1/B2/B3 PHYSICAL PRODUCER RESIDUAL
--
-- The shell decomposition and producer bundling below are DASHI extensions
-- extracted from the current non-Round B frontier. They do not assert that the
-- corresponding physical shell payments exist.  The selected periodic source
-- and each producer predicate are fixed externally.
------------------------------------------------------------------------

record CanonicalB123PhysicalProducerResidual
    (SelectedPeriodicSource : Set)
    (selectedSource : SelectedPeriodicSource)
    (B1PhysicalProducer : SelectedPeriodicSource → Set)
    (B2PhysicalProducer : SelectedPeriodicSource → Set)
    (B3PhysicalProducer : SelectedPeriodicSource → Set) : Set₁ where
  field
    b1PhysicalProducer : B1PhysicalProducer selectedSource
    b2PhysicalProducer : B2PhysicalProducer selectedSource
    b3PhysicalProducer : B3PhysicalProducer selectedSource
