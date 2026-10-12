module DASHI.Cognition.ClinicToStreetsConsumerNonDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair

------------------------------------------------------------------------
-- CONSUMER-RELATIVE NON-DESCENT OF ATOMISED CAUSAL PROVENANCE
--
-- The Clinic-to-Streets max-cut already shows that an atomising
-- interpretation can erase the structural coordinate while retaining the
-- intimate and intrapsychic coordinates.  This owner reuses the repository's
-- canonical consumer-descent machinery to state the stronger, but still
-- purely structural, consequence:
--
--   if a declared consumer needs the structural coordinate, the atomised
--   observer is not sufficient for that consumer and the consumer cannot
--   factor through the atomised surface.
--
-- The landed consumer-fibre-repair machinery then sharpens reskilling:
-- restoring the structural residual repairs this exact consumer collision,
-- and every sufficient repair of the collision must separate the two worlds.
--
-- These are finite information-loss/repair theorems.  They are not evidence
-- that any concrete therapy, institution, narrative, or population realizes
-- the illustrated causal worlds.
------------------------------------------------------------------------

record CausalWorld : Set where
  constructor causal-world
  field
    structuralCoordinate : Bool
    intimateCoordinate : Bool
    intrapsychicCoordinate : Bool

open CausalWorld public

fullStructuralWorld : CausalWorld
fullStructuralWorld = causal-world true true true

sameSurfaceWithoutStructuralWorld : CausalWorld
sameSurfaceWithoutStructuralWorld = causal-world false true true

AtomisedSurface : Set
AtomisedSurface = Bool × Bool

atomisingObserver : CausalWorld → AtomisedSurface
atomisingObserver world =
  intimateCoordinate world , intrapsychicCoordinate world

structuralConsumer : CausalWorld → Bool
structuralConsumer = structuralCoordinate

-- The two worlds collide after atomisation but differ for the declared
-- structural-provenance consumer.
canonicalAtomisingNonDescent :
  Descent.ConsumerNonDescentWitness atomisingObserver structuralConsumer
canonicalAtomisingNonDescent =
  Descent.consumerNonDescentWitness
    fullStructuralWorld
    sameSurfaceWithoutStructuralWorld
    refl
    (λ ())

atomisingObserverBlocksStructuralSufficiency :
  Descent.ConsumerSufficient atomisingObserver structuralConsumer → ⊥
atomisingObserverBlocksStructuralSufficiency =
  Descent.nonDescentWitnessBlocksSufficiency canonicalAtomisingNonDescent

atomisingObserverBlocksStructuralFactorisation :
  Descent.FactorsThrough atomisingObserver structuralConsumer → ⊥
atomisingObserverBlocksStructuralFactorisation =
  Descent.nonDescentWitnessBlocksFactorization canonicalAtomisingNonDescent

------------------------------------------------------------------------
-- Exact repair / reskilling cross-pollination.
------------------------------------------------------------------------

structuralResidual : CausalWorld → Bool
structuralResidual = structuralCoordinate

-- The canonical pair observer (atomised surface, restored structural residual)
-- is sufficient for the structural consumer on all CausalWorld states.
structuralResidualRepairsAtomisation :
  Repair.RefinementRepairs atomisingObserver structuralResidual structuralConsumer
structuralResidualRepairsAtomisation left right samePairedObservation =
  cong proj₂ samePairedObservation

-- Conversely, any refinement that genuinely restores structural-consumer
-- sufficiency must distinguish the exact collision exposed above.  Separation
-- of this one collision remains necessary, not sufficient for every consumer.
anySufficientRepairSeparatesCanonicalCollision :
  ∀ {Refinement : Set} {refine : CausalWorld → Refinement} →
  Repair.RefinementRepairs atomisingObserver refine structuralConsumer →
  refine fullStructuralWorld ≡ refine sameSurfaceWithoutStructuralWorld →
  ⊥
anySufficientRepairSeparatesCanonicalCollision repaired sameRefinement =
  Repair.refinementRepairSeparatesWitness
    canonicalAtomisingNonDescent
    repaired
    sameRefinement

-- Retaining the full causal world is sufficient for the same consumer.  This
-- is the maximal simple repair direction: enrichment may restore consumer
-- sufficiency without asserting that the richer observer is world-complete.
contextObserver : CausalWorld → CausalWorld
contextObserver world = world

contextObserverIsStructurallySufficient :
  Descent.ConsumerSufficient contextObserver structuralConsumer
contextObserverIsStructurallySufficient left right refl = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ClinicConsumerNonDescentBoundary : Set where
  constructor clinic-consumer-non-descent-boundary
  field
    atomisedStructuralNonDescentPaid : Bool
    structuralResidualRepairPaid : Bool
    everySufficientRepairSeparatesCanonicalCollision : Bool
    fullContextStructuralSufficiencyPaid : Bool
    oneCollisionSeparationProvesGlobalConsumerSufficiency : Bool
    oneConsumerDefinesWorldCompleteness : Bool
    finiteCollisionEstablishesEmpiricalCausality : Bool
    nonDescentEstablishesDeliberateIntent : Bool

canonicalClinicConsumerNonDescentBoundary : ClinicConsumerNonDescentBoundary
canonicalClinicConsumerNonDescentBoundary =
  clinic-consumer-non-descent-boundary
    true true true true false false false false
