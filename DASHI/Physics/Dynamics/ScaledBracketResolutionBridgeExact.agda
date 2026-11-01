{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.ScaledBracketResolutionBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as BRR
import DASHI.Physics.Dynamics.YanchukSelectedCrossSectionBracketExact as YB

------------------------------------------------------------------------
-- Generic bridge from an adjacent scaled bracket to a resolution relation.
--
-- This is deliberately arithmetic-only.  An external analytic or validated
-- numerical layer must still prove the selected basin predicate at the two
-- endpoint states before a BasinBoundaryResolutionWitness can be constructed.
------------------------------------------------------------------------

data BracketEndpoint : Set where
  lowerEndpoint : BracketEndpoint
  upperEndpoint : BracketEndpoint

data BracketResolution : Set where
  oneGridUnit : BracketResolution

data EndpointNear :
  BracketResolution →
  BracketEndpoint →
  BracketEndpoint →
  Set where
  lowerNearLower :
    EndpointNear oneGridUnit lowerEndpoint lowerEndpoint
  upperNearUpper :
    EndpointNear oneGridUnit upperEndpoint upperEndpoint
  lowerNearUpper :
    EndpointNear oneGridUnit lowerEndpoint upperEndpoint
  upperNearLower :
    EndpointNear oneGridUnit upperEndpoint lowerEndpoint

endpointResolutionGeometry :
  BRR.ResolutionGeometry
    BracketEndpoint BracketResolution
endpointResolutionGeometry =
  record { Near = EndpointNear }

record OppositeEndpointPredicateReceipt
  (Predicate : BracketEndpoint → Set) : Set where
  field
    lowerHas : Predicate lowerEndpoint
    upperLacks : ¬ Predicate upperEndpoint

open OppositeEndpointPredicateReceipt public

opposite-adjacent-endpoints-give-boundary-witness :
  ∀ {Predicate : BracketEndpoint → Set} →
  OppositeEndpointPredicateReceipt Predicate →
  BRR.BasinBoundaryResolutionWitness
    endpointResolutionGeometry
    Predicate
    oneGridUnit
opposite-adjacent-endpoints-give-boundary-witness receipt =
  record
    { inside = lowerEndpoint
    ; outside = upperEndpoint
    ; withinResolution = lowerNearUpper
    ; insideHas = lowerHas receipt
    ; outsideLacks = upperLacks receipt
    }

opposite-adjacent-endpoints-refute-one-grid-robustness :
  ∀ {Predicate : BracketEndpoint → Set} →
  (receipt : OppositeEndpointPredicateReceipt Predicate) →
  ¬ BRR.RobustAt
      endpointResolutionGeometry
      Predicate
      oneGridUnit
      lowerEndpoint
opposite-adjacent-endpoints-refute-one-grid-robustness receipt =
  BRR.boundary-witness-refutes-robustness
    (opposite-adjacent-endpoints-give-boundary-witness receipt)

------------------------------------------------------------------------
-- Selected arithmetic attachment.
--
-- The Yanchuk selected bracket is exactly one grid unit wide at denominator
-- 65536000000000000.  This does NOT provide OppositeEndpointPredicateReceipt;
-- that is the remaining analytic/validated-numerics weld.
------------------------------------------------------------------------

selectedArithmeticBracket :
  YB.AdjacentScaledBracket
selectedArithmeticBracket =
  YB.selectedBracket

selectedArithmeticWidth :
  YB.UnitGridWidth selectedArithmeticBracket
selectedArithmeticWidth =
  YB.selectedBracketWidthIsOneGridUnit
