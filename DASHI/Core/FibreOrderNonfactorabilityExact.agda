module DASHI.Core.FibreOrderNonfactorabilityExact where

------------------------------------------------------------------------
-- HIDDEN UPDATE ORDER CANNOT DESCEND THROUGH A FIXED SURFACE
--
-- Two carrier operators may each preserve a coarse projection while failing to
-- commute upstairs.  At any witness point where the two composite endpoints
-- differ, the coarse surface cannot reconstruct which ordered endpoint was
-- produced.
--
-- Mathematical precedent / structural analogue:
-- Kenneth G. Wilson, "Confinement of quarks",
-- DOI 10.1103/PhysRevD.10.2445.
-- Frank Wilczek; A. Zee,
-- "Appearance of Gauge Structure in Simple Dynamical Systems",
-- DOI 10.1103/PhysRevLett.52.2111.
--
-- Non-Abelian parallel transport/holonomy is path ordered precisely because
-- the transported transformations need not commute while the base loop may
-- return to the same point.  The finite theorem below shares that algebraic
-- shape, but it does NOT construct a connection, curvature, principal bundle,
-- Wilson loop, Lie group, or gauge field.  Hence "holonomy analogue" is a
-- provenance/calibration statement, not a semantic identification.
--
-- This is domain-neutral algebra.  It can be instantiated by legal decision
-- dynamics, access/braid dynamics, or other fibre-preserving systems without
-- identifying their semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.IntersectionalNonFactorability as NF

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
