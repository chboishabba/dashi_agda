module DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND94 / SAME-OBJECT PHYSICAL GALERKIN INSTANTIATION
--
-- `NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact` already defines
-- the actual finite periodic NS coefficient
--
--   F_N(u)(j) = -nu |j|^2 u(j) + projectedNonlinearity(j).
--
-- Round94's literal product-rule theorem is instantiated here with
--
--   rho_j = nu |j|^2,
--   f_j   = projectedNonlinearity(j).
--
-- Hence for every physical triad p+q=k the same literal Waleffe amplitude
--
--   Z = <u_k , u_p x u_q>
--
-- has vector-field tangent
--
--   dZ = -nu (|k|^2+|p|^2+|q|^2) Z + F_network,
--
-- where F_network is exactly the three product-rule slots obtained by feeding
-- the repository's projected nonlinear Fourier network into k,p,q.  No
-- isolated-triad approximation or statistical closure is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent

physicalDecayRate :
  ∀ {r} {F : C3.RealField r} →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Carrier F
physicalDecayRate physicalSystem mode =
  C3.multiply F
    (PhysicalField.viscosity physicalSystem)
    (C3.normSquared
      (Audit.inverseSquare (PhysicalField.finiteSystem physicalSystem)) mode)

physicalVelocity :
  ∀ {r} {F : C3.RealField r} →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Complex3 F
physicalVelocity physicalSystem =
  Audit.velocityAt (PhysicalField.finiteSystem physicalSystem)

physicalNetworkForcingMode :
  ∀ {r} {F : C3.RealField r} →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → C3.Complex3 F
physicalNetworkForcingMode physicalSystem =
  Audit.projectedNonlinearity (PhysicalField.finiteSystem physicalSystem)

literalCoefficientIsDampedPlusNetwork :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (mode : Z3.FourierMode) →
  PhysicalField.literalViscousQuadraticCoefficient physicalSystem mode
  ≡
  Tangent.dampedPlusForcing
    (physicalDecayRate physicalSystem mode)
    (physicalVelocity physicalSystem mode)
    (physicalNetworkForcingMode physicalSystem mode)
literalCoefficientIsDampedPlusNetwork physicalSystem mode = refl

physicalTriadComplexAmplitude :
  ∀ {r} {F : C3.RealField r} →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → C3.Complex F
physicalTriadComplexAmplitude physicalSystem tau =
  Tangent.complexAmplitude
    (physicalVelocity physicalSystem (Physical.k tau))
    (physicalVelocity physicalSystem (Physical.p tau))
    (physicalVelocity physicalSystem (Physical.q tau))

physicalTriadNetworkForcing :
  ∀ {r} {F : C3.RealField r} →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → C3.Complex F
physicalTriadNetworkForcing physicalSystem tau =
  Tangent.networkForcing
    (physicalVelocity physicalSystem (Physical.k tau))
    (physicalVelocity physicalSystem (Physical.p tau))
    (physicalVelocity physicalSystem (Physical.q tau))
    (physicalNetworkForcingMode physicalSystem (Physical.k tau))
    (physicalNetworkForcingMode physicalSystem (Physical.p tau))
    (physicalNetworkForcingMode physicalSystem (Physical.q tau))

physicalTriadAmplitudeTangent :
  ∀ {r} {F : C3.RealField r} →
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Physical.PhysicalTriadIncidence → C3.Complex F
physicalTriadAmplitudeTangent physicalSystem tau =
  Tangent.amplitudeTangent
    (physicalVelocity physicalSystem (Physical.k tau))
    (physicalVelocity physicalSystem (Physical.p tau))
    (physicalVelocity physicalSystem (Physical.q tau))
    (PhysicalField.literalViscousQuadraticCoefficient
      physicalSystem (Physical.k tau))
    (PhysicalField.literalViscousQuadraticCoefficient
      physicalSystem (Physical.p tau))
    (PhysicalField.literalViscousQuadraticCoefficient
      physicalSystem (Physical.q tau))

physicalTriadWaleffeAmplitudeDampedNetworkTangent :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (tau : Physical.PhysicalTriadIncidence) →
  physicalTriadAmplitudeTangent physicalSystem tau
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (Tangent.totalNegativeDecay
        (physicalDecayRate physicalSystem (Physical.k tau))
        (physicalDecayRate physicalSystem (Physical.p tau))
        (physicalDecayRate physicalSystem (Physical.q tau)))
      (physicalTriadComplexAmplitude physicalSystem tau))
    (physicalTriadNetworkForcing physicalSystem tau)
physicalTriadWaleffeAmplitudeDampedNetworkTangent physicalSystem tau =
  trans
    (cong₂
      (Tangent.amplitudeTangent
        (physicalVelocity physicalSystem (Physical.k tau))
        (physicalVelocity physicalSystem (Physical.p tau))
        (physicalVelocity physicalSystem (Physical.q tau)))
      (cong₂ _,_
        (literalCoefficientIsDampedPlusNetwork physicalSystem (Physical.k tau))
        (literalCoefficientIsDampedPlusNetwork physicalSystem (Physical.p tau)))
      (literalCoefficientIsDampedPlusNetwork physicalSystem (Physical.q tau)))
    (Tangent.amplitudeTangentDampedNetwork
      (physicalDecayRate physicalSystem (Physical.k tau))
      (physicalDecayRate physicalSystem (Physical.p tau))
      (physicalDecayRate physicalSystem (Physical.q tau))
      (physicalVelocity physicalSystem (Physical.k tau))
      (physicalVelocity physicalSystem (Physical.p tau))
      (physicalVelocity physicalSystem (Physical.q tau))
      (physicalNetworkForcingMode physicalSystem (Physical.k tau))
      (physicalNetworkForcingMode physicalSystem (Physical.p tau))
      (physicalNetworkForcingMode physicalSystem (Physical.q tau)))

-- A simpler proof term avoiding tuple transport is supplied as the canonical
-- theorem below.  The preceding expanded statement records the intended exact
-- same-object formula; this helper rewrites each slot definitionally.
physicalTriadWaleffeAmplitudeDampedNetworkTangentDirect :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (tau : Physical.PhysicalTriadIncidence) →
  Tangent.amplitudeTangent
    (physicalVelocity physicalSystem (Physical.k tau))
    (physicalVelocity physicalSystem (Physical.p tau))
    (physicalVelocity physicalSystem (Physical.q tau))
    (Tangent.dampedPlusForcing
      (physicalDecayRate physicalSystem (Physical.k tau))
      (physicalVelocity physicalSystem (Physical.k tau))
      (physicalNetworkForcingMode physicalSystem (Physical.k tau)))
    (Tangent.dampedPlusForcing
      (physicalDecayRate physicalSystem (Physical.p tau))
      (physicalVelocity physicalSystem (Physical.p tau))
      (physicalNetworkForcingMode physicalSystem (Physical.p tau)))
    (Tangent.dampedPlusForcing
      (physicalDecayRate physicalSystem (Physical.q tau))
      (physicalVelocity physicalSystem (Physical.q tau))
      (physicalNetworkForcingMode physicalSystem (Physical.q tau)))
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (Tangent.totalNegativeDecay
        (physicalDecayRate physicalSystem (Physical.k tau))
        (physicalDecayRate physicalSystem (Physical.p tau))
        (physicalDecayRate physicalSystem (Physical.q tau)))
      (physicalTriadComplexAmplitude physicalSystem tau))
    (physicalTriadNetworkForcing physicalSystem tau)
physicalTriadWaleffeAmplitudeDampedNetworkTangentDirect physicalSystem tau =
  Tangent.amplitudeTangentDampedNetwork
    (physicalDecayRate physicalSystem (Physical.k tau))
    (physicalDecayRate physicalSystem (Physical.p tau))
    (physicalDecayRate physicalSystem (Physical.q tau))
    (physicalVelocity physicalSystem (Physical.k tau))
    (physicalVelocity physicalSystem (Physical.p tau))
    (physicalVelocity physicalSystem (Physical.q tau))
    (physicalNetworkForcingMode physicalSystem (Physical.k tau))
    (physicalNetworkForcingMode physicalSystem (Physical.p tau))
    (physicalNetworkForcingMode physicalSystem (Physical.q tau))

round94PhysicalGalerkinWaleffeAmplitudeTangentClosed : Bool
round94PhysicalGalerkinWaleffeAmplitudeTangentClosed = true

round94PhysicalGalerkinNetworkForcingIdentified : Bool
round94PhysicalGalerkinNetworkForcingIdentified = true

round94PhysicalGalerkinWaleffeAmplitudeTangentClosedIsTrue :
  round94PhysicalGalerkinWaleffeAmplitudeTangentClosed ≡ true
round94PhysicalGalerkinWaleffeAmplitudeTangentClosedIsTrue = refl

round94PhysicalGalerkinNetworkForcingIdentifiedIsTrue :
  round94PhysicalGalerkinNetworkForcingIdentified ≡ true
round94PhysicalGalerkinNetworkForcingIdentifiedIsTrue = refl
