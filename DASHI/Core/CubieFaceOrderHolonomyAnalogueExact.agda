module DASHI.Core.CubieFaceOrderHolonomyAnalogueExact where

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.FibreOrderNonfactorabilityExact as Order
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

------------------------------------------------------------------------
-- CUBIE-FACE ORDER / HOLONOMY ANALOGUE
--
-- Mathematical precedent:
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445-2459.
-- DOI: 10.1103/PhysRevD.10.2445
--
-- Frank Wilczek; A. Zee,
-- "Appearance of Gauge Structure in Simple Dynamical Systems",
-- Physical Review Letters 52 (1984), 2111-2114.
-- DOI: 10.1103/PhysRevLett.52.2111
--
-- The exact theorem below is only an algebraic/cubical analogue: two hidden
-- surface-preserving transports around a local face fail to commute.  No
-- connection, curvature, gauge field, Wilson loop, or quantum cognition is
-- constructed by this module.
------------------------------------------------------------------------

data FaceState : Set where
  root aOnly bOnly aAfterB bAfterA : FaceState

data FaceSurface : Set where coarseFace : FaceSurface

data FaceEvidence : Set where noFaceEvidence : FaceEvidence

projectFace : FaceState → FaceSurface
projectFace _ = coarseFace

faceCore : Fibre.FibreRestrictionCore
faceCore = Fibre.fibreRestrictionCore
  FaceState
  FaceSurface
  FaceEvidence
  projectFace
  (λ surface → FaceState)
  (λ evidence surface → FaceState)
  true
  false

firstTransport : Dynamics.CarrierOperator faceCore
firstTransport root = aOnly
firstTransport bOnly = aAfterB
firstTransport state = state

secondTransport : Dynamics.CarrierOperator faceCore
secondTransport root = bOnly
secondTransport aOnly = bAfterA
secondTransport state = state

firstPreservesFace : Dynamics.SurfaceInvariant faceCore firstTransport
firstPreservesFace state = refl

secondPreservesFace : Dynamics.SurfaceInvariant faceCore secondTransport
secondPreservesFace state = refl

orderedEndpointsDiffer :
  firstTransport (secondTransport root)
  ≡ secondTransport (firstTransport root) → ⊥
orderedEndpointsDiffer ()

orderedEndpointsShareCoarseFace :
  Fibre.project faceCore (firstTransport (secondTransport root))
  ≡ Fibre.project faceCore (secondTransport (firstTransport root))
orderedEndpointsShareCoarseFace = refl

cubieFaceOrderNonfactorability :
  NF.NonFactorabilityWitness
    (Order.orderedSurface firstTransport secondTransport root)
    (Order.orderedEndpoint firstTransport secondTransport root)
cubieFaceOrderNonfactorability =
  Order.orderEndpointNonfactorability
    firstPreservesFace
    secondPreservesFace
    root
    orderedEndpointsDiffer

coarseFaceCannotDecodeTransportOrder :
  NF.FactorsThrough
    (Order.orderedSurface firstTransport secondTransport root)
    (Order.orderedEndpoint firstTransport secondTransport root) → ⊥
coarseFaceCannotDecodeTransportOrder =
  Order.surfaceCannotDecodeOrderedEndpoint
    firstPreservesFace
    secondPreservesFace
    root
    orderedEndpointsDiffer

------------------------------------------------------------------------
-- Link the local face explicitly to the repository's rank-three cubie language.
------------------------------------------------------------------------

localCubieAddress : Hyper.AxisBlock 3
localCubieAddress =
  Hyper.block-cons Hyper.axis-mid
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-low Hyper.block-root))

record CubieHolonomyBoundary : Set where
  constructor cubieHolonomyBoundary
  field
    noncommutingHiddenTransportExists : Bool
    coarseFaceErasesOrder : Bool
    literalGaugeConnectionConstructed : Bool
    wilsonLoopComputed : Bool
    quantumBrainClaimed : Bool

canonicalCubieHolonomyBoundary : CubieHolonomyBoundary
canonicalCubieHolonomyBoundary =
  cubieHolonomyBoundary true true false false false
