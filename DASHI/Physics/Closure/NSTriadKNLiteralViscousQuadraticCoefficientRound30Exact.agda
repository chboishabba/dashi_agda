module DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact where

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
-- Construct the actual finite-mode Navier--Stokes right-hand side
--
--   F_N(u)(k)
--     = -nu |k|^2 u(k)
--       + sum_{p+q=k} -i P_k[(u(p) dot q)u(q)]
--
-- from the repository's exhaustive physical output fibre.  Assuming only
-- that the input retained velocity is transverse, the diagonal viscous term,
-- the exhaustive projected nonlinear fold, and their sum are proved
-- transverse.  Mapping this coefficient over the literal retained mode list
-- constructs a `ReconstructedPhysicalState`; the nonzero-mode proof is
-- transported from the concrete Galerkin system rather than resupplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as Nonlinear

record PhysicalFiniteComplex3GalerkinSystem
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    finiteSystem : Audit.FiniteComplex3GalerkinSystem F
    viscosity : C3.Carrier F

    retainedVelocityTransverse : ∀ mode →
      mode Cube.∈ Audit.modes finiteSystem →
      C3.bilinearDot3
        (C3.modeVector (Audit.integerEmbedding finiteSystem) mode)
        (Audit.velocityAt finiteSystem mode)
      ≡ C3.complexZero F

open PhysicalFiniteComplex3GalerkinSystem public

viscousScalar :
  ∀ {r} {F : C3.RealField r} →
  PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Complex F
viscousScalar {F = F} physicalSystem mode =
  C3.realEmbed F
    (C3.negate F
      (C3.multiply F
        (viscosity physicalSystem)
        (C3.normSquared
          (Audit.inverseSquare (finiteSystem physicalSystem)) mode)))

literalViscousCoefficient :
  ∀ {r} {F : C3.RealField r} →
  PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Complex3 F
literalViscousCoefficient physicalSystem mode =
  C3.complex3Scale
    (viscousScalar physicalSystem mode)
    (Audit.velocityAt (finiteSystem physicalSystem) mode)

literalViscousQuadraticCoefficient :
  ∀ {r} {F : C3.RealField r} →
  PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Complex3 F
literalViscousQuadraticCoefficient physicalSystem mode =
  C3.complex3Add
    (literalViscousCoefficient physicalSystem mode)
    (Audit.projectedNonlinearity (finiteSystem physicalSystem) mode)

literalViscousCoefficientTransverse :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F)
    mode →
  mode Cube.∈ Audit.modes (finiteSystem physicalSystem) →
  C3.bilinearDot3
    (C3.modeVector
      (Audit.integerEmbedding (finiteSystem physicalSystem)) mode)
    (literalViscousCoefficient physicalSystem mode)
  ≡ C3.complexZero F
literalViscousCoefficientTransverse {F = F}
    physicalSystem mode member =
  trans
    (Scaling.bilinearDot3ScaleRight
      (viscousScalar physicalSystem mode)
      (C3.modeVector
        (Audit.integerEmbedding (finiteSystem physicalSystem)) mode)
      (Audit.velocityAt (finiteSystem physicalSystem) mode))
    (trans
      (cong (C3.complexMultiply (viscousScalar physicalSystem mode))
        (retainedVelocityTransverse physicalSystem mode member))
      (Field.complexMultiplyZeroRight
        (viscousScalar physicalSystem mode)))

literalViscousQuadraticCoefficientTransverse :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F)
    mode →
  (member : mode Cube.∈ Audit.modes (finiteSystem physicalSystem)) →
  C3.bilinearDot3
    (C3.modeVector
      (Audit.integerEmbedding (finiteSystem physicalSystem)) mode)
    (literalViscousQuadraticCoefficient physicalSystem mode)
  ≡ C3.complexZero F
literalViscousQuadraticCoefficientTransverse
    physicalSystem mode member =
  Nonlinear.transverseAdd
    (C3.modeVector
      (Audit.integerEmbedding (finiteSystem physicalSystem)) mode)
    (literalViscousCoefficient physicalSystem mode)
    (Audit.projectedNonlinearity (finiteSystem physicalSystem) mode)
    (literalViscousCoefficientTransverse physicalSystem mode member)
    (Nonlinear.projectedNonlinearityTransverseExact
      (finiteSystem physicalSystem) mode
      (Audit.modeNonzero (finiteSystem physicalSystem) mode member))

literalTransverseCoefficient :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F)
    mode →
  mode Cube.∈ Audit.modes (finiteSystem physicalSystem) →
  Phase.TransverseModeCoefficient F
    (Audit.integerEmbedding (finiteSystem physicalSystem))
literalTransverseCoefficient physicalSystem mode member =
  Phase.transverse-mode-coefficient
    mode
    (literalViscousQuadraticCoefficient physicalSystem mode)
    (literalViscousQuadraticCoefficientTransverse
      physicalSystem mode member)

mapLiteralCoefficients :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F)
    (source : List Z3.FourierMode) →
  (∀ mode → mode Cube.∈ source →
    mode Cube.∈ Audit.modes (finiteSystem physicalSystem)) →
  List (Phase.TransverseModeCoefficient F
    (Audit.integerEmbedding (finiteSystem physicalSystem)))
mapLiteralCoefficients physicalSystem [] sourceIncluded = []
mapLiteralCoefficients physicalSystem (mode ∷ rest) sourceIncluded =
  literalTransverseCoefficient physicalSystem mode
    (sourceIncluded mode (Cube.here refl))
  ∷ mapLiteralCoefficients physicalSystem rest
      (λ selected member → sourceIncluded selected (Cube.there member))

literalCoefficientList :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F) →
  List (Phase.TransverseModeCoefficient F
    (Audit.integerEmbedding (finiteSystem physicalSystem)))
literalCoefficientList physicalSystem =
  mapLiteralCoefficients physicalSystem
    (Audit.modes (finiteSystem physicalSystem))
    (λ mode member → member)

mappedCoefficientModeNonzero :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F)
    (source : List Z3.FourierMode)
    (sourceIncluded : ∀ mode → mode Cube.∈ source →
      mode Cube.∈ Audit.modes (finiteSystem physicalSystem))
    coefficient →
  coefficient State.∈
    mapLiteralCoefficients physicalSystem source sourceIncluded →
  Z3.NonZeroMode (Phase.coefficientMode coefficient)
mappedCoefficientModeNonzero physicalSystem [] sourceIncluded coefficient ()
mappedCoefficientModeNonzero physicalSystem (mode ∷ rest)
    sourceIncluded coefficient (State.here coefficientExact) =
  subst Z3.NonZeroMode
    (sym (cong Phase.coefficientMode coefficientExact))
    (Audit.modeNonzero (finiteSystem physicalSystem) mode
      (sourceIncluded mode (Cube.here refl)))
mappedCoefficientModeNonzero physicalSystem (mode ∷ rest)
    sourceIncluded coefficient (State.there member) =
  mappedCoefficientModeNonzero physicalSystem rest
    (λ selected selectedMember →
      sourceIncluded selected (Cube.there selectedMember))
    coefficient member

literalGalerkinPhysicalState :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalFiniteComplex3GalerkinSystem F) →
  State.ReconstructedPhysicalState F
    (Audit.integerEmbedding (finiteSystem physicalSystem))
literalGalerkinPhysicalState physicalSystem =
  State.reconstructed-physical-state
    (literalCoefficientList physicalSystem)
    (mappedCoefficientModeNonzero physicalSystem
      (Audit.modes (finiteSystem physicalSystem))
      (λ mode member → member))

literalViscousQuadraticCoefficientClosed : Bool
literalViscousQuadraticCoefficientClosed = true

literalViscousQuadraticCoefficientClosedIsTrue :
  literalViscousQuadraticCoefficientClosed ≡ true
literalViscousQuadraticCoefficientClosedIsTrue = refl
