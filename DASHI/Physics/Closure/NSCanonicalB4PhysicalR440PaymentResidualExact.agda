{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440PaymentResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES B4 PHYSICAL R440 PAYMENT RESIDUAL
--
-- The literal periodic Clay target is source-facing; the identification of the
-- final B4 signed noncore/core payment as the irreducible analytic leaf is a
-- DASHI extension distilled from the current non-Round B frontier.
--
-- The selected physical source and payment predicate are fixed externally.
------------------------------------------------------------------------

record CanonicalB4PhysicalR440PaymentResidual
    (SelectedPeriodicSource : Set)
    (selectedSource : SelectedPeriodicSource)
    (PhysicalR440NoncoreCorePayment : SelectedPeriodicSource → Set) : Set₁ where
  field
    physicalR440NoncoreCorePayment :
      PhysicalR440NoncoreCorePayment selectedSource
