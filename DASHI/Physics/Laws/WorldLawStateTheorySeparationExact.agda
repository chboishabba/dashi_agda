module DASHI.Physics.Laws.WorldLawStateTheorySeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.WorldRepresentationSeparationExact as World
import DASHI.Physics.Laws.PhysicalLawCore as Law
import DASHI.Physics.Limits.PhysicsLimitCommutingSquare as Limit

------------------------------------------------------------------------
-- WORLD REGULARITY / LAW DESCRIPTION / STATE / INITIAL CONDITION
--
-- PhysicalLawSurface is a formal/empirical description surface. It is not
-- definitionally the world regularity it aims to describe. Likewise a law is
-- not an initial condition and a change of state is not a change of law.
------------------------------------------------------------------------

record WorldLawStatePresentation : Set₁ where
  constructor world-law-state-presentation
  field
    WorldState : Set
    LawDescription : Set
    InitialCondition : Set
    worldState : WorldState
    lawDescription : LawDescription
    initialCondition : InitialCondition
    presentationReference : String

open WorldLawStatePresentation public

data WorldEqualsLawPermission : Set where
data LawEqualsInitialConditionPermission : Set where
data StateChangeImpliesLawChangePermission : Set where
data TheoryAgreementImpliesExactTheoryEquivalencePermission : Set where

worldDoesNotDefinitionallyEqualLaw :
  WorldEqualsLawPermission → ⊥
worldDoesNotDefinitionallyEqualLaw ()

lawDoesNotDefinitionallyEqualInitialCondition :
  LawEqualsInitialConditionPermission → ⊥
lawDoesNotDefinitionallyEqualInitialCondition ()

stateChangeDoesNotRequireLawChange :
  StateChangeImpliesLawChangePermission → ⊥
stateChangeDoesNotRequireLawChange ()

agreementDoesNotManufactureExactTheoryEquivalence :
  TheoryAgreementImpliesExactTheoryEquivalencePermission → ⊥
agreementDoesNotManufactureExactTheoryEquivalence ()

------------------------------------------------------------------------
-- Reuse PhysicalLawCore's independent state/context/parameter/law coordinates.
------------------------------------------------------------------------

record LawStateCoordinateReceipt (surface : Law.PhysicalLawSurface) : Set₁ where
  constructor law-state-coordinate-receipt
  field
    context : Law.PhysicalLawSurface.Context surface
    parameter : Law.PhysicalLawSurface.Parameter surface
    initial final : Law.PhysicalLawSurface.State surface
    initialAdmissible :
      Law.PhysicalLawSurface.admissible surface context parameter initial
    finalAdmissible :
      Law.PhysicalLawSurface.admissible surface context parameter final
    evolution :
      Law.PhysicalLawSurface.evolves surface context parameter initial final
    sameLawSurfaceReference : String

open LawStateCoordinateReceipt public

------------------------------------------------------------------------
-- Theory-to-theory recovery is separately typed. Exact equivalence requires
-- exact commutation; effective recovery requires a controlled residual.
------------------------------------------------------------------------

record TheoryRecoveryBoundary : Set where
  constructor theory-recovery-boundary
  field
    exactRecoveryNeedsCommutingSquare : Bool
    exactRecoveryNeedsCommutingSquareIsTrue :
      exactRecoveryNeedsCommutingSquare ≡ true
    effectiveRecoveryNeedsControlledResidual : Bool
    effectiveRecoveryNeedsControlledResidualIsTrue :
      effectiveRecoveryNeedsControlledResidual ≡ true
    sharedFiniteCarrierAloneIdentifiesTheories : Bool
    sharedFiniteCarrierAloneIdentifiesTheoriesIsFalse :
      sharedFiniteCarrierAloneIdentifiesTheories ≡ false

open TheoryRecoveryBoundary public

canonicalTheoryRecoveryBoundary : TheoryRecoveryBoundary
canonicalTheoryRecoveryBoundary =
  theory-recovery-boundary true refl true refl false refl

worldBoundary : World.WorldRepresentationBoundary
worldBoundary = World.canonicalWorldRepresentationBoundary

------------------------------------------------------------------------
-- Gravity-reading boundary: "gravity existed before theories of gravity" is
-- represented as independence of the world coordinate from possession of a
-- theory coordinate. This does not assert Newtonian force ontology, GR
-- ontology, or any future theory as definitionally identical to the world.
------------------------------------------------------------------------

record GravityPreTheoryBoundary : Set where
  constructor gravity-pre-theory-boundary
  field
    fallingRequiresHumanTheory : Bool
    fallingRequiresHumanTheoryIsFalse :
      fallingRequiresHumanTheory ≡ false
    changingGravityTheoryChangesPastWorldByDefinition : Bool
    changingGravityTheoryChangesPastWorldByDefinitionIsFalse :
      changingGravityTheoryChangesPastWorldByDefinition ≡ false
    currentBestTheoryIsDefinitionallyWorldOntology : Bool
    currentBestTheoryIsDefinitionallyWorldOntologyIsFalse :
      currentBestTheoryIsDefinitionallyWorldOntology ≡ false

canonicalGravityPreTheoryBoundary : GravityPreTheoryBoundary
canonicalGravityPreTheoryBoundary =
  gravity-pre-theory-boundary false refl false refl false refl
