module DASHI.Moonshine.OggSSPP2OrientedInertiaModuliProblemExact where

------------------------------------------------------------------------
-- p=2 ORIENTED UNORIENTED-INERTIA ENRICHED MODULI PROBLEM
--
-- DASHI DEFINITION, CLASSICALLY SOURCED INGREDIENTS
--
-- Fix the unique coarse supersingular elliptic-curve class in characteristic 2.
-- An enriched marked object consists of:
--
--   1. one of the two orientations of an imaginary quadratic order;
--   2. one inertia sector, i.e. a conjugacy class of an automorphism;
--   3. forgetting loop direction identifies [g] with [g^{-1}].
--
-- Hence the coarse sector classifier is:
--
--   two orientation sheets
--     x
--   five loop-reversal orbits of binary-tetrahedral inertia
--
--   = ten sectors.
--
-- This is a specific DASHI-defined moduli/groupoid problem assembled from
-- standard classical constructions.  It is NOT Gamma0(4), and no external
-- source is credited with naming this exact product or linking it to Monster
-- exponent arithmetic.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as Ten
import DASHI.Moonshine.OggSSPP2OrientedUnorientedInertiaStackCandidateExact as StackCandidate
import DASHI.Moonshine.OggSSPP2RetainedCMMarkedSourceExact as P2Source
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Enriched object and coarse-sector classifier.
------------------------------------------------------------------------

record P2EnrichedMarkedObject : Set where
  constructor p2-enriched-marked-object
  field
    orientation :
      Ten.ClassicalQuadraticOrientation
    inertiaClass :
      Inertia.BinaryTetrahedralConjugacyClass

open P2EnrichedMarkedObject public

data P2EnrichedSector : Set where
  p2-enriched-sector :
    Ten.ClassicalQuadraticOrientation ->
    Inertia.BinaryTetrahedralInversionOrbit ->
    P2EnrichedSector

sectorOf :
  P2EnrichedMarkedObject ->
  P2EnrichedSector
sectorOf object =
  p2-enriched-sector
    (orientation object)
    (Inertia.quotientByInversion (inertiaClass object))

------------------------------------------------------------------------
-- 2. Coarse sector carrier is exactly the existing 2 x 5 carrier.
------------------------------------------------------------------------

sectorToOrientedInertia :
  P2EnrichedSector ->
  Ten.P2OrientedInertiaState
sectorToOrientedInertia (p2-enriched-sector orientation orbit) =
  orientation , orbit

orientedInertiaToSector :
  Ten.P2OrientedInertiaState ->
  P2EnrichedSector
orientedInertiaToSector (orientation , orbit) =
  p2-enriched-sector orientation orbit

sectorRoundTrip :
  (sector : P2EnrichedSector) ->
  orientedInertiaToSector (sectorToOrientedInertia sector) ≡ sector
sectorRoundTrip (p2-enriched-sector orientation orbit) = refl

orientedInertiaRoundTrip :
  (state : Ten.P2OrientedInertiaState) ->
  sectorToOrientedInertia (orientedInertiaToSector state) ≡ state
orientedInertiaRoundTrip (orientation , orbit) = refl

sectorToDASHITenState :
  P2EnrichedSector ->
  P2Source.P2CMMarkedState
sectorToDASHITenState sector =
  Ten.toP2CMMarkedState (sectorToOrientedInertia sector)

dashiTenStateToSector :
  P2Source.P2CMMarkedState ->
  P2EnrichedSector
dashiTenStateToSector state =
  orientedInertiaToSector (Ten.fromP2CMMarkedState state)

sectorDASHIRoundTrip :
  (sector : P2EnrichedSector) ->
  dashiTenStateToSector (sectorToDASHITenState sector) ≡ sector
sectorDASHIRoundTrip sector =
  trans
    (cong orientedInertiaToSector
      (Ten.orientedInertiaRoundTrip (sectorToOrientedInertia sector)))
    (sectorRoundTrip sector)

dashiSectorRoundTrip :
  (state : P2Source.P2CMMarkedState) ->
  sectorToDASHITenState (dashiTenStateToSector state) ≡ state
dashiSectorRoundTrip =
  Ten.p2CMRoundTrip

------------------------------------------------------------------------
-- 3. What this moduli problem does and does not mean.
------------------------------------------------------------------------

data EnrichedModuliProblemIsStandardNamedStack : Set where
data EnrichedSectorEqualsFullInertiaObject : Set where
data CoarseSectorClassificationErasesAllStackStabilizers : Set where
data EnrichedModuliProblemProvesMonsterResidual : Set where
data InertiaSectorLabelsAreBase369Semantics : Set where

notPromotedToStandardNamedStack :
  EnrichedModuliProblemIsStandardNamedStack -> ⊥
notPromotedToStandardNamedStack ()

sectorIsNotFullInertiaObject :
  EnrichedSectorEqualsFullInertiaObject -> ⊥
sectorIsNotFullInertiaObject ()

coarseSectorClassifierDoesNotAssertTrivialStabilizers :
  CoarseSectorClassificationErasesAllStackStabilizers -> ⊥
coarseSectorClassifierDoesNotAssertTrivialStabilizers ()

moduliProblemDoesNotProveMonsterResidual :
  EnrichedModuliProblemProvesMonsterResidual -> ⊥
moduliProblemDoesNotProveMonsterResidual ()

inertiaLabelsDoNotAcquireBase369Semantics :
  InertiaSectorLabelsAreBase369Semantics -> ⊥
inertiaLabelsDoNotAcquireBase369Semantics ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record P2OrientedInertiaModuliProblemBoundary : Set where
  constructor p2-oriented-inertia-moduli-problem-boundary
  field
    uniqueCoarseSupersingularBaseClassical : Bool
    orientationDoubletClassical : Bool
    inertiaConjugacyClassFrameworkClassical : Bool
    binaryTetrahedralSevenClassesClassical : Bool
    loopReversalFiveSectorQuotientConstructed : Bool
    exactTenSectorClassifierConstructed : Bool
    exactRechartToDASHITenStateProved : Bool
    specificEnrichedModuliProblemDefined : Bool
    standardNamedClassicalStackClaimed : Bool
    gamma04IdentityClaimed : Bool
    monsterArithmeticIdentityClaimed : Bool
    base369SemanticIdentityClaimed : Bool

canonicalP2OrientedInertiaModuliProblemBoundary :
  P2OrientedInertiaModuliProblemBoundary
canonicalP2OrientedInertiaModuliProblemBoundary =
  p2-oriented-inertia-moduli-problem-boundary
    true true true true true true true true false false false false
