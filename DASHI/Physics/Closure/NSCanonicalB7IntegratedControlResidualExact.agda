{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB7IntegratedControlResidualExact where

------------------------------------------------------------------------
-- CANONICAL NAVIER--STOKES B7 INTEGRATED-CONTROL RESIDUAL
--
-- DASHI extension: the current non-Round B frontier records a preferred
-- Q4-integrated-control + E-positive-amplitude route and a Q5 signed-quintic
-- fallback.  This owner preserves that logical alternative without promoting
-- either route.  All predicates are fixed externally.
------------------------------------------------------------------------

data CanonicalB7IntegratedControlResidual
    (SelectedPeriodicSource : Set)
    (selectedSource : SelectedPeriodicSource)
    (Q4IntegratedSpacetimeControl : SelectedPeriodicSource → Set)
    (EPositiveGlobalAmplitudeControl : SelectedPeriodicSource → Set)
    (Q5SignedQuinticFallback : SelectedPeriodicSource → Set) : Set₁ where
  preferredQ4EControl :
    Q4IntegratedSpacetimeControl selectedSource →
    EPositiveGlobalAmplitudeControl selectedSource →
    CanonicalB7IntegratedControlResidual
      SelectedPeriodicSource selectedSource
      Q4IntegratedSpacetimeControl EPositiveGlobalAmplitudeControl
      Q5SignedQuinticFallback
  q5SignedQuinticFallback :
    Q5SignedQuinticFallback selectedSource →
    CanonicalB7IntegratedControlResidual
      SelectedPeriodicSource selectedSource
      Q4IntegratedSpacetimeControl EPositiveGlobalAmplitudeControl
      Q5SignedQuinticFallback
