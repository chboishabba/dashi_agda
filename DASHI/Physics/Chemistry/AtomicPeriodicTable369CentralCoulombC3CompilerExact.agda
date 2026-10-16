module DASHI.Physics.Chemistry.AtomicPeriodicTable369CentralCoulombC3CompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Mechanism-neutral central/pair-potential symmetry compiler.
--
-- A central one-particle term depends only on radius.  A Coulomb pair term
-- depends only on inter-particle separation.  Therefore any same-object action
-- preserving those two geometric observables preserves the corresponding
-- potential terms.  This is a mathematical compiler only: it does not identify
-- the finite ternary/charge action with a spatial rotation, does not build the
-- kinetic operator, and does not project a continuum Hamiltonian into a finite
-- p-shell basis.
------------------------------------------------------------------------

record RadialPairGeometry : Set₁ where
  field
    Position : Set
    Radius : Set
    Separation : Set

    rotate : Position -> Position
    radius : Position -> Radius
    separation : Position -> Position -> Separation

    rotationOrderThree :
      (x : Position) -> rotate (rotate (rotate x)) ≡ x

    preservesRadius :
      (x : Position) -> radius (rotate x) ≡ radius x

    preservesSeparation :
      (x y : Position) ->
      separation (rotate x) (rotate y) ≡ separation x y

open RadialPairGeometry public

record CentralPairPotential (G : RadialPairGeometry) : Set₁ where
  open RadialPairGeometry G
  field
    OneBodyValue : Set
    PairValue : Set
    centralPotential : Radius -> OneBodyValue
    pairPotential : Separation -> PairValue

  oneBodyTerm : Position -> OneBodyValue
  oneBodyTerm x = centralPotential (radius x)

  twoBodyTerm : Position -> Position -> PairValue
  twoBodyTerm x y = pairPotential (separation x y)

open CentralPairPotential public

centralTermInvariant :
  (G : RadialPairGeometry) ->
  (V : CentralPairPotential G) ->
  (x : Position G) ->
  oneBodyTerm V (rotate G x) ≡ oneBodyTerm V x
centralTermInvariant G V x =
  cong (CentralPairPotential.centralPotential V)
    (preservesRadius G x)

pairTermInvariant :
  (G : RadialPairGeometry) ->
  (V : CentralPairPotential G) ->
  (x y : Position G) ->
  twoBodyTerm V (rotate G x) (rotate G y) ≡ twoBodyTerm V x y
pairTermInvariant G V x y =
  cong (CentralPairPotential.pairPotential V)
    (preservesSeparation G x y)

------------------------------------------------------------------------
-- Same-object handoff expected from the continuous SO(3) sibling machinery.
--
-- The current torque/SO(3) PR can be a future producer of a concrete spatial
-- rotation satisfying the geometric obligations.  It is not imported here as
-- theorem authority because this atomic branch is stacked independently.
------------------------------------------------------------------------

record AtomicSpatialC3CoulombHandoff : Set₁ where
  field
    geometry : RadialPairGeometry
    potential : CentralPairPotential geometry

    sameSpatialRotationAsAnalyticPTriplet : Bool
    finiteChargeActionIntertwinedWithSpatialRepresentation : Bool
    kineticTermInvariantPaid : Bool
    continuumToPTripletProjectionPaid : Bool

open AtomicSpatialC3CoulombHandoff public

record CentralCoulombC3Boundary : Set where
  constructor centralCoulombC3Boundary
  field
    radiusPreservingActionImpliesCentralPotentialInvariant : Bool
    separationPreservingActionImpliesPairPotentialInvariant : Bool
    sourceIndependentGeometryCompilerPaid : Bool

    finiteChargeTransportIsSpatialRotationByDefinition : Bool
    kineticOperatorPaidHere : Bool
    projectedPTripletCoulombMatrixPaidHere : Bool
    interactingGroundState369RecognitionPaid : Bool

open CentralCoulombC3Boundary public

canonicalCentralCoulombC3Boundary : CentralCoulombC3Boundary
canonicalCentralCoulombC3Boundary =
  centralCoulombC3Boundary
    true true true
    false false false false

chargeTransportIsSpatialRotationByDefinitionIsFalse :
  finiteChargeTransportIsSpatialRotationByDefinition canonicalCentralCoulombC3Boundary
  ≡ false
chargeTransportIsSpatialRotationByDefinitionIsFalse = refl
