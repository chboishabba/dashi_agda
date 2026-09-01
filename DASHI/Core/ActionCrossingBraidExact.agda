module DASHI.Core.ActionCrossingBraidExact where

------------------------------------------------------------------------
-- ACTION-CROSSING BRAID
--
-- Domain-neutral carrier:
--   * persistent entities/histories are strands;
--   * an action involving strands is represented by a crossing event;
--   * an ordered action history is a crossing trace;
--   * a coarse endpoint need not determine the crossing trace.
--
-- "Braid" is used as a structural path/order grammar.  This module does not
-- construct a topological braid group, Yang-Baxter representation, or claim
-- that every physical/social/computational action literally is a braid.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF

record ActionCrossingSurface : Set₁ where
  constructor action-crossing-surface
  field
    Trace : Set
    Endpoint : Set
    Provenance : Set
    endpoint : Trace → Endpoint
    provenance : Trace → Provenance

open ActionCrossingSurface public

record SameEndpointDifferentProvenance
    (surface : ActionCrossingSurface) : Set where
  constructor same-endpoint-different-provenance
  field
    leftTrace rightTrace : Trace surface
    sameEndpoint : endpoint surface leftTrace ≡ endpoint surface rightTrace
    differentProvenance :
      provenance surface leftTrace ≡ provenance surface rightTrace → ⊥

open SameEndpointDifferentProvenance public

endpointCannotRecoverCrossingProvenance :
  ∀ {surface : ActionCrossingSurface} →
  SameEndpointDifferentProvenance surface →
  INF.FactorsThrough (endpoint surface) (provenance surface) → ⊥
endpointCannotRecoverCrossingProvenance witness =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      (leftTrace witness)
      (rightTrace witness)
      (sameEndpoint witness)
      (differentProvenance witness))

record ActionCrossingBoundary : Set where
  constructor action-crossing-boundary
  field
    actionOrderCanBeFirstClass : Set
    endpointMayForgetPath : Set

-- Empty promotion types make the nonclaims theorem-visible.
data EveryActionLiterallyTopologicalBraid : Set where

data CrossingGrammarConstructsBraidGroup : Set where

data SameEndpointDeterminesCrossingHistory : Set where

everyActionIsNotPromotedToLiteralTopologicalBraid :
  EveryActionLiterallyTopologicalBraid → ⊥
everyActionIsNotPromotedToLiteralTopologicalBraid ()

crossingGrammarDoesNotConstructBraidGroup :
  CrossingGrammarConstructsBraidGroup → ⊥
crossingGrammarDoesNotConstructBraidGroup ()

sameEndpointDoesNotGenerallyDetermineCrossingHistory :
  SameEndpointDeterminesCrossingHistory → ⊥
sameEndpointDoesNotGenerallyDetermineCrossingHistory ()
