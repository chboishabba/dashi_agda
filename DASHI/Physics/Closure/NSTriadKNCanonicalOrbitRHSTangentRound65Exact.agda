module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitRHSTangentRound65Exact where

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
-- ROUND 65 / A1 FINITE-CARRIER ADVANCE
--
-- Round63 proved that the literal Galerkin RHS has exactly as many coefficients
-- as the canonical one-representative-per-{k,-k} coordinate list.  Count
-- equality alone is not invariance.  Here we prove the stronger pointwise fact:
-- EVERY output coefficient of the literal RHS has its mode in that exact same
-- canonical orbit list.
--
-- Thus the finite vector field is tangent to the fixed canonical coordinate
-- carrier selected at the current cutoff.  The remaining A1 existence problem
-- is genuinely the finite-dimensional ODE/Picard trajectory and the subsequent
-- differentiated localized identity, not another mode-enumeration closure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffPhysicalVectorFieldRound62Exact as Adapter
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitGalerkinRHSRound63Exact as RHS
open import Relation.Binary.PropositionalEquality using (subst; sym)

canonicalOrbitRHSCoefficientModeIncluded :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  coefficient State.∈ RHS.canonicalOrbitRHSCoefficients family state →
  Phase.coefficientMode coefficient Cube.∈
    Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state))
canonicalOrbitRHSCoefficientModeIncluded family state coefficient member =
  let
    witness = RHS.canonicalOrbitRHSCoefficientWitness
      family state coefficient member
    sourceMember = Concrete.sourceMembership witness
  in
  subst
    (λ mode → mode Cube.∈
      Orbit.canonicalCutoffOrbitModes
        (Canonical.cutoff (Canonical.datumAt family state)))
    (sym (Concrete.modeExact witness))
    sourceMember

record CanonicalOrbitRHSTangent
    {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E) : Set r where
  field
    everyDerivativeCoordinateRetained :
      ∀ coefficient →
      coefficient State.∈ RHS.canonicalOrbitRHSCoefficients family state →
      Phase.coefficientMode coefficient Cube.∈
        Orbit.canonicalCutoffOrbitModes
          (Canonical.cutoff (Canonical.datumAt family state))

open CanonicalOrbitRHSTangent public

canonicalOrbitRHSIsTangent :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E) →
  CanonicalOrbitRHSTangent family state
canonicalOrbitRHSIsTangent family state = record
  { everyDerivativeCoordinateRetained =
      canonicalOrbitRHSCoefficientModeIncluded family state
  }

round65CanonicalOrbitGalerkinRHSPointwiseTangent : Bool
round65CanonicalOrbitGalerkinRHSPointwiseTangent = true

round65CanonicalOrbitGalerkinRHSPointwiseTangentIsTrue :
  round65CanonicalOrbitGalerkinRHSPointwiseTangent ≡ true
round65CanonicalOrbitGalerkinRHSPointwiseTangentIsTrue = refl
