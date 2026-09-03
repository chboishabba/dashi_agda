module DASHI.Physics.QuantumVacuum.FiniteCasimirNonFactorabilityCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.NonFactorabilityCompositionExact as NFC
import DASHI.Physics.QuantumVacuum.FiniteCasimirModeDifferenceFixtureExact as Fixture

------------------------------------------------------------------------
-- CROSS-POLLINATION
--
-- The finite Casimir fixture is an exact instance of the repository's generic
-- non-factorability calculus.  Field identity is the coarse observer; the raw
-- finite doubled vacuum aggregate is the boundary-sensitive phenomenon.
------------------------------------------------------------------------

fieldProjection :
  Fixture.FiniteBoundaryModeFabric → Fixture.FieldToken
fieldProjection = Fixture.field

vacuumAggregateProjection :
  Fixture.FiniteBoundaryModeFabric → Nat
vacuumAggregateProjection = Fixture.doubledVacuumGroundAggregate

finiteCasimirGenericNonFactorability :
  NF.NonFactorabilityWitness
    fieldProjection
    vacuumAggregateProjection
finiteCasimirGenericNonFactorability =
  NF.nonFactorabilityWitness
    Fixture.freeFabric
    Fixture.cavityFabric
    Fixture.sameField
    (Fixture.distinguish Fixture.aggregateDifference)

fieldIdentityCannotDetermineVacuumAggregate :
  NF.FactorsThrough fieldProjection vacuumAggregateProjection → ⊥
fieldIdentityCannotDetermineVacuumAggregate =
  NF.witnessRulesOutEveryFlatFactorisation
    finiteCasimirGenericNonFactorability

------------------------------------------------------------------------
-- Stronger closure: no relabelling, score, hash, category, or other
-- post-processing of field identity alone can restore the erased boundary
-- distinction.
------------------------------------------------------------------------

fieldRechartCannotRecoverVacuumAggregate :
  ∀ {Recharted : Set} →
  (rechart : Fixture.FieldToken → Recharted) →
  NF.FactorsThrough
    (λ fabric → rechart (fieldProjection fabric))
    vacuumAggregateProjection →
  ⊥
fieldRechartCannotRecoverVacuumAggregate rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart finiteCasimirGenericNonFactorability

fieldCoarseningPreservesVacuumNonFactorability :
  ∀ {Surface : Set} →
  (coarsen : Fixture.FieldToken → Surface) →
  NF.NonFactorabilityWitness
    (λ fabric → coarsen (fieldProjection fabric))
    vacuumAggregateProjection
fieldCoarseningPreservesVacuumNonFactorability coarsen =
  NFC.postcomposeNonFactorability
    coarsen finiteCasimirGenericNonFactorability

------------------------------------------------------------------------
-- Positive repair criterion: the observer must add genuinely new information.
-- The paired field/boundary observer separates the fixture pair.
------------------------------------------------------------------------

fieldBoundaryProjection :
  Fixture.FiniteBoundaryModeFabric →
  Fixture.FieldToken × Fixture.BoundaryToken
fieldBoundaryProjection fabric =
  Fixture.field fabric , Fixture.boundary fabric

fieldBoundaryPairSeparatesFixture :
  fieldBoundaryProjection Fixture.freeFabric ≡
  fieldBoundaryProjection Fixture.cavityFabric → ⊥
fieldBoundaryPairSeparatesFixture ()
