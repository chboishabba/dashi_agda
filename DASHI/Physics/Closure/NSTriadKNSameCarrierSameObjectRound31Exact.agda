module DASHI.Physics.Closure.NSTriadKNSameCarrierSameObjectRound31Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Strengthen the Round-30 state-indexed Galerkin builder by requiring the
-- finite system to use the coefficients stored in the dependent physical
-- state itself.  Positive modes are read literally; negative modes are the
-- repository's conjugate reconstruction; and the retained mode list is the
-- exact positive/negative reconstruction list.
--
-- This rules out the quantifier error
--
--   for every state there exists some unrelated finite system
--
-- being consumed as though one canonical physical vector field had been
-- constructed.  Forgetting the stronger certificate recovers the Round-30
-- builder and therefore its literal viscous-plus-quadratic vector field.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete

reconstructedStateModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  State.ReconstructedPhysicalState F E → List Z3.FourierMode
reconstructedStateModes {F = F} {E = E} state =
  go (State.positiveOrbitCoefficients state)
  where
  go :
    List (Phase.TransverseModeCoefficient F E) →
    List Z3.FourierMode
  go [] = []
  go (coefficient ∷ rest) =
    Phase.coefficientMode coefficient
    ∷ Phase.reconstructedNegativeMode coefficient
    ∷ go rest

record SameCarrierSameObjectGalerkinBuilder
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    physicalSystemAt :
      State.ReconstructedPhysicalState F E →
      Coefficient.PhysicalFiniteComplex3GalerkinSystem F

    embeddingExact : ∀ state →
      Audit.integerEmbedding
        (Coefficient.finiteSystem (physicalSystemAt state))
      ≡ E

    positiveVelocityExact :
      ∀ state coefficient →
      coefficient State.∈ State.positiveOrbitCoefficients state →
      Audit.velocityAt
        (Coefficient.finiteSystem (physicalSystemAt state))
        (Phase.coefficientMode coefficient)
      ≡ Phase.coefficientValue coefficient

    negativeVelocityExact :
      ∀ state coefficient →
      coefficient State.∈ State.positiveOrbitCoefficients state →
      Audit.velocityAt
        (Coefficient.finiteSystem (physicalSystemAt state))
        (Phase.reconstructedNegativeMode coefficient)
      ≡ Phase.reconstructedNegativeValue coefficient

    retainedModesExact : ∀ state →
      Audit.modes
        (Coefficient.finiteSystem (physicalSystemAt state))
      ≡ reconstructedStateModes state

open SameCarrierSameObjectGalerkinBuilder public

forgetSameCarrierSameObject :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  SameCarrierSameObjectGalerkinBuilder F E →
  Concrete.StateIndexedPhysicalGalerkinSystem F E
forgetSameCarrierSameObject builder = record
  { Concrete.StateIndexedPhysicalGalerkinSystem.physicalSystemAt =
      physicalSystemAt builder
  ; Concrete.StateIndexedPhysicalGalerkinSystem.embeddingExact =
      embeddingExact builder
  }

sameObjectPositiveVelocity :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : SameCarrierSameObjectGalerkinBuilder F E)
    state coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  Audit.velocityAt
    (Coefficient.finiteSystem (physicalSystemAt builder state))
    (Phase.coefficientMode coefficient)
  ≡ Phase.coefficientValue coefficient
sameObjectPositiveVelocity builder =
  positiveVelocityExact builder

sameObjectNegativeVelocity :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : SameCarrierSameObjectGalerkinBuilder F E)
    state coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  Audit.velocityAt
    (Coefficient.finiteSystem (physicalSystemAt builder state))
    (Phase.reconstructedNegativeMode coefficient)
  ≡ Phase.reconstructedNegativeValue coefficient
sameObjectNegativeVelocity builder =
  negativeVelocityExact builder

sameObjectRetainedModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : SameCarrierSameObjectGalerkinBuilder F E)
    state →
  Audit.modes
    (Coefficient.finiteSystem (physicalSystemAt builder state))
  ≡ reconstructedStateModes state
sameObjectRetainedModes builder =
  retainedModesExact builder

sameObjectPhysicalGalerkinVectorField :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  SameCarrierSameObjectGalerkinBuilder F E →
  State.ReconstructedPhysicalState F E →
  State.ReconstructedPhysicalState F E
sameObjectPhysicalGalerkinVectorField builder =
  Concrete.concretePhysicalGalerkinVectorField
    (forgetSameCarrierSameObject builder)

sameCarrierSameObjectInterfaceClosed : Bool
sameCarrierSameObjectInterfaceClosed = true

canonicalSameCarrierSameObjectBuilderConstructed : Bool
canonicalSameCarrierSameObjectBuilderConstructed = false

sameCarrierSameObjectInterfaceClosedIsTrue :
  sameCarrierSameObjectInterfaceClosed ≡ true
sameCarrierSameObjectInterfaceClosedIsTrue = refl

canonicalSameCarrierSameObjectBuilderConstructedIsFalse :
  canonicalSameCarrierSameObjectBuilderConstructed ≡ false
canonicalSameCarrierSameObjectBuilderConstructedIsFalse = refl
