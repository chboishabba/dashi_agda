module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalAttributionCoordinatesValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalAttributionCoordinatesExact as Coordinates

boundary = Coordinates.canonicalAdKPhysicalAttributionCoordinatesBoundary

_ : Coordinates.usesTypedDashiKnowledgeCoordinates boundary ≡ true
_ = refl

_ : Coordinates.doiQidDeweyRemainCoordinatesOnly boundary ≡ true
_ = refl

_ : Coordinates.unresolvedDeweyRemainsExplicit boundary ≡ true
_ = refl

_ : Coordinates.unresolvedQidRemainsExplicit boundary ≡ true
_ = refl

_ : Coordinates.externalIdentityCreatesScientificPayment boundary ≡ false
_ = refl

_ : Coordinates.deweyAdjacencyCreatesScientificDependency boundary ≡ false
_ = refl
