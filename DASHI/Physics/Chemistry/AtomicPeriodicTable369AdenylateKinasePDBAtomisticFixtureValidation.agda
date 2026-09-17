module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBAtomisticFixtureValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBAtomisticFixtureExact as Fixture

boundary = Fixture.canonicalAdKPDBAtomisticFixtureBoundary

_ : Fixture.openAndClosedPdbObjectsRetained boundary ≡ true
_ = refl

_ : Fixture.coordinateManifestationSeparatedFromEntryIdentity boundary ≡ true
_ = refl

_ : Fixture.multiChainAmbiguityRetained boundary ≡ true
_ = refl

_ : Fixture.sourceEndpointTriplesRetained boundary ≡ true
_ = refl

_ : Fixture.pdbEntryIdentitySelectsCanonicalChain boundary ≡ false
_ = refl

_ : Fixture.sourceEndpointTripleEqualsCoordinateRecomputation boundary ≡ false
_ = refl
