module DASHI.Core.FibreOrderNonfactorabilityExact where

------------------------------------------------------------------------
-- HIDDEN UPDATE ORDER CANNOT DESCEND THROUGH A FIXED SURFACE
--
-- Two carrier operators may each preserve a coarse projection while failing to
-- commute upstairs.  At any witness point where the two composite endpoints
-- differ, the coarse surface cannot reconstruct which ordered endpoint was
-- produced.
--
-- This is domain-neutral algebra.  It can be instantiated by legal decision
-- dynamics, access/braid dynamics, or other fibre-preserving systems without
-- identifying their semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- 1. Order carrier and composite endpoints.
------------------------------------------------------------------------

data UpdateOrder : Set where
  firstAfterSecond secondAfterFirst : UpdateOrder

orderedEndpoint :
  ∀ {core : Fibre.FibreRestrictionCore} →
  Dynamics.CarrierOperator core →
  Dynamics.CarrierOperator core →
  Fibre.Carrier core →
  UpdateOrder →
  Fibre.Carrier core
orderedEndpoint first second x firstAfterSecond = first (second x)
orderedEndpoint first second x secondAfterFirst = second (first x)

orderedSurface :
  ∀ {core : Fibre.FibreRestrictionCore} →
  Dynamics.CarrierOperator core →
  Dynamics.CarrierOperator core →
  Fibre.Carrier core →
  UpdateOrder →
  Fibre.Surface core
orderedSurface {core} first second x order =
  Fibre.project core (orderedEndpoint first second x order)

------------------------------------------------------------------------
-- 2. Surface invariance composes.
------------------------------------------------------------------------

compositeSurfaceInvariant :
  ∀ {core : Fibre.FibreRestrictionCore}
    {first second : Dynamics.CarrierOperator core} →
  Dynamics.SurfaceInvariant core first →
  Dynamics.SurfaceInvariant core second →
  (x : Fibre.Carrier core) →
  Fibre.project core (first (second x)) ≡ Fibre.project core x
compositeSurfaceInvariant firstInvariant secondInvariant x =
  trans
    (firstInvariant (second x))
    (secondInvariant x)

orderedCompositesShareSurface :
  ∀ {core : Fibre.FibreRestrictionCore}
    {first second : Dynamics.CarrierOperator core} →
  Dynamics.SurfaceInvariant core first →
  Dynamics.SurfaceInvariant core second →
  (x : Fibre.Carrier core) →
  orderedSurface first second x firstAfterSecond
  ≡ orderedSurface first second x secondAfterFirst
orderedCompositesShareSurface firstInvariant secondInvariant x =
  trans
    (compositeSurfaceInvariant firstInvariant secondInvariant x)
    (sym (compositeSurfaceInvariant secondInvariant firstInvariant x))

------------------------------------------------------------------------
-- 3. Noncommuting hidden endpoints produce an exact non-factorability witness.
------------------------------------------------------------------------

orderEndpointNonfactorability :
  ∀ {core : Fibre.FibreRestrictionCore}
    {first second : Dynamics.CarrierOperator core} →
  Dynamics.SurfaceInvariant core first →
  Dynamics.SurfaceInvariant core second →
  (x : Fibre.Carrier core) →
  (first (second x) ≡ second (first x) → ⊥) →
  NF.NonFactorabilityWitness
    (orderedSurface first second x)
    (orderedEndpoint first second x)
orderEndpointNonfactorability firstInvariant secondInvariant x noncommutes =
  NF.nonFactorabilityWitness
    firstAfterSecond
    secondAfterFirst
    (orderedCompositesShareSurface firstInvariant secondInvariant x)
    noncommutes

surfaceCannotDecodeOrderedEndpoint :
  ∀ {core : Fibre.FibreRestrictionCore}
    {first second : Dynamics.CarrierOperator core} →
  Dynamics.SurfaceInvariant core first →
  Dynamics.SurfaceInvariant core second →
  (x : Fibre.Carrier core) →
  (first (second x) ≡ second (first x) → ⊥) →
  NF.FactorsThrough
    (orderedSurface first second x)
    (orderedEndpoint first second x) →
  ⊥
surfaceCannotDecodeOrderedEndpoint firstInvariant secondInvariant x noncommutes =
  NF.witnessRulesOutEveryFlatFactorisation
    (orderEndpointNonfactorability
      firstInvariant secondInvariant x noncommutes)

------------------------------------------------------------------------
-- 4. Same statement directly from fibre automorphisms.
------------------------------------------------------------------------

automorphismOrderNonfactorability :
  ∀ {core : Fibre.FibreRestrictionCore} →
  (first second : Dynamics.FibreAutomorphism core) →
  (x : Fibre.Carrier core) →
  (Dynamics.forward first (Dynamics.forward second x)
    ≡ Dynamics.forward second (Dynamics.forward first x) → ⊥) →
  NF.NonFactorabilityWitness
    (orderedSurface (Dynamics.forward first) (Dynamics.forward second) x)
    (orderedEndpoint (Dynamics.forward first) (Dynamics.forward second) x)
automorphismOrderNonfactorability first second x noncommutes =
  orderEndpointNonfactorability
    (Dynamics.forwardPreservesSurface first)
    (Dynamics.forwardPreservesSurface second)
    x
    noncommutes
