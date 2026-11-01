module DASHI.Computation.PathfindingFibreCoreExact where

-- Shared pathfinding fibre interface.
-- A fine algorithm state may contain scheduling/order data that a correctness
-- consumer does not observe.  Quotienting is lawful only when observation
-- invariance under the declared residual action is proved.

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Bool using (Bool; false; true)

record PathfindingFibreSystem : Set₁ where
  constructor pathfindingFibreSystem
  field
    FineState Observation ResidualSymmetry : Set
    identity : ResidualSymmetry
    compose : ResidualSymmetry → ResidualSymmetry → ResidualSymmetry
    act : ResidualSymmetry → FineState → FineState
    observe : FineState → Observation
    identityActs : (x : FineState) → act identity x ≡ x
    actionComposes :
      (g h : ResidualSymmetry) (x : FineState) →
      act (compose g h) x ≡ act g (act h x)
    observationInvariant :
      (g : ResidualSymmetry) (x : FineState) →
      observe (act g x) ≡ observe x

open PathfindingFibreSystem public

record SameResidualOrbit
  (F : PathfindingFibreSystem)
  (x y : FineState F) : Set where
  constructor sameResidualOrbit
  field
    symmetry : ResidualSymmetry F
    actsTo : act F symmetry x ≡ y

open SameResidualOrbit public

sameResidualOrbitSameObservation :
  (F : PathfindingFibreSystem) →
  (x y : FineState F) →
  SameResidualOrbit F x y →
  observe F x ≡ observe F y
sameResidualOrbitSameObservation F x y orbit =
  trans
    (sym (observationInvariant F (symmetry orbit) x))
    (cong (observe F) (actsTo orbit))

record PathfindingFibreBoundary : Set where
  constructor pathfindingFibreBoundary
  field
    quotientRequiresInvarianceProof : Bool
    quotientRequiresInvarianceProofIsTrue :
      quotientRequiresInvarianceProof ≡ true
    equalCardinalityImpliesSameAlgorithmicRole : Bool
    equalCardinalityImpliesSameAlgorithmicRoleIsFalse :
      equalCardinalityImpliesSameAlgorithmicRole ≡ false
    residualScheduleMayBeDiscardedWithoutWitness : Bool
    residualScheduleMayBeDiscardedWithoutWitnessIsFalse :
      residualScheduleMayBeDiscardedWithoutWitness ≡ false

canonicalPathfindingFibreBoundary : PathfindingFibreBoundary
canonicalPathfindingFibreBoundary =
  pathfindingFibreBoundary true refl false refl false refl
