module DASHI.Moonshine.VNaturalOrbifoldConstruction where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA

------------------------------------------------------------------------
-- FLM-shaped orbifold construction surface for V^natural.
--
-- This module does not postulate that the moonshine module exists.  Instead it
-- isolates the exact construction data required by the standard Leech-lattice
-- involution/orbifold route:
--
--   V_Λ  -- fixed-point VOA under θ
--       \-- θ-twisted module, integral/even sector
--
--   V^natural = V_Λ^+ ⊕ (V_Λ^T)^+.
--
-- The direct-sum carrier below is constructive.  Promotion to a VOA requires
-- the supplied closure, locality, Jacobi, conformal, and simplicity witnesses.

record VOAInvolution (V : VOA.VertexOperatorAlgebra) : Setω where
  field
    theta :
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V) →
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V)
    involutive : ∀ x → theta (theta x) ≡ x
    preservesVacuum : Set
    preservesConformalVector : Set
    preservesVertexModes : Set
    preservesGrading : Set

open VOAInvolution public

record FixedPointVOA
  (V : VOA.VertexOperatorAlgebra)
  (involution : VOAInvolution V) : Setω where
  field
    fixedCarrier : Set
    includeFixed :
      fixedCarrier →
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V)
    fixedByTheta :
      ∀ x →
      VOAInvolution.theta involution (includeFixed x) ≡ includeFixed x
    fixedVOA : VOA.VertexOperatorAlgebra
    inclusionPreservesVOA : Set

open FixedPointVOA public

record TwistedModule
  (V : VOA.VertexOperatorAlgebra)
  (involution : VOAInvolution V) : Setω where
  field
    Scalar : Set
    Carrier : Set
    TwistIndex : Set
    twistedMode :
      VOA.GradedModule.Carrier (VOA.VertexOperatorAlgebra.gradedModule V) →
      TwistIndex → Carrier → Carrier
    twistedLowerTruncation : Set
    twistedVacuumCompatibility : Set
    twistedTranslationCovariance : Set
    twistedJacobiIdentity : Set
    thetaMonodromy : Set
    conformalWeight : Carrier → Set

open TwistedModule public

record TwistedEvenSector
  {V : VOA.VertexOperatorAlgebra}
  {involution : VOAInvolution V}
  (twisted : TwistedModule V involution) : Setω where
  field
    CarrierPlus : Set
    includePlus : CarrierPlus → TwistedModule.Carrier twisted
    integralWeight : ∀ x → TwistedModule.conformalWeight twisted (includePlus x)
    thetaEven : Set

open TwistedEvenSector public

OrbifoldCarrier :
  ∀ {V involution}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) → Set
OrbifoldCarrier fixed twisted plus =
  FixedPointVOA.fixedCarrier fixed ⊎ TwistedEvenSector.CarrierPlus plus

record OrbifoldVOAAssembly
  {V : VOA.VertexOperatorAlgebra}
  {involution : VOAInvolution V}
  (fixed : FixedPointVOA V involution)
  (twisted : TwistedModule V involution)
  (plus : TwistedEvenSector twisted) : Setω where
  field
    orbifoldVOA : VOA.VertexOperatorAlgebra
    identifyCarrier :
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
      → OrbifoldCarrier fixed twisted plus
    includeFixedSummand :
      FixedPointVOA.fixedCarrier fixed →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
    includeTwistedSummand :
      TwistedEvenSector.CarrierPlus plus →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule orbifoldVOA)
    fixedSummandIdentifies :
      ∀ x → identifyCarrier (includeFixedSummand x) ≡ inj₁ x
    twistedSummandIdentifies :
      ∀ x → identifyCarrier (includeTwistedSummand x) ≡ inj₂ x
    mixedVertexProductsClosed : Set
    localityAcrossSummands : Set
    JacobiAcrossSummands : Set
    conformalVectorAgrees : Set
    centralCharge24 : Set
    CFTType : Set
    holomorphic : Set
    simple : Set

open OrbifoldVOAAssembly public

record LeechLatticeVOAInput : Setω where
  field
    leechLatticeVOA : VOA.VertexOperatorAlgebra
    leechInvolution : VOAInvolution leechLatticeVOA
    fixedPoint : FixedPointVOA leechLatticeVOA leechInvolution
    canonicalTwistedModule : TwistedModule leechLatticeVOA leechInvolution
    twistedEvenSector : TwistedEvenSector canonicalTwistedModule
    leechRootless : Set
    latticeVOACentralCharge24 : Set

open LeechLatticeVOAInput public

record VNaturalConstruction : Setω where
  field
    leechInput : LeechLatticeVOAInput
    orbifoldAssembly :
      OrbifoldVOAAssembly
        (LeechLatticeVOAInput.fixedPoint leechInput)
        (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
        (LeechLatticeVOAInput.twistedEvenSector leechInput)

  Vnatural : VOA.VertexOperatorAlgebra
  Vnatural = OrbifoldVOAAssembly.orbifoldVOA orbifoldAssembly

  VnaturalCarrier : Set
  VnaturalCarrier =
    OrbifoldCarrier
      (LeechLatticeVOAInput.fixedPoint leechInput)
      (LeechLatticeVOAInput.canonicalTwistedModule leechInput)
      (LeechLatticeVOAInput.twistedEvenSector leechInput)

  centralCharge24 : Set
  centralCharge24 = OrbifoldVOAAssembly.centralCharge24 orbifoldAssembly

  holomorphic : Set
  holomorphic = OrbifoldVOAAssembly.holomorphic orbifoldAssembly

  simple : Set
  simple = OrbifoldVOAAssembly.simple orbifoldAssembly

open VNaturalConstruction public

constructVNatural :
  (input : LeechLatticeVOAInput) →
  OrbifoldVOAAssembly
    (LeechLatticeVOAInput.fixedPoint input)
    (LeechLatticeVOAInput.canonicalTwistedModule input)
    (LeechLatticeVOAInput.twistedEvenSector input) →
  VNaturalConstruction
constructVNatural input assembly =
  record
    { leechInput = input
    ; orbifoldAssembly = assembly
    }
