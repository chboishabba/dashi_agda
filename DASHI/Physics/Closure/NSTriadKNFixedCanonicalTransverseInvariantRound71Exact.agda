module DASHI.Physics.Closure.NSTriadKNFixedCanonicalTransverseInvariantRound71Exact where

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
-- ROUND 71 / TRANSVERSE SUBSPACE INVARIANCE
--
-- On the fixed autonomous reality carrier, define transversality only on the
-- canonical positive representatives.  Reality reconstructs the negative sheet.
--
-- If u is transverse on those positive modes, then for every canonical output k:
--
-- * the viscous term -nu |k|^2 u(k) is transverse by scalar multiplication;
-- * the complete literal projected nonlinearity is transverse for arbitrary
--   input velocities by the existing Round30 Leray-output theorem;
-- * their sum is transverse.
--
-- The exact positive lookup theorem identifies the output state's stored value
-- with rawCanonicalRHSAt.  Hence the fixed vector field maps the transverse
-- subspace to itself.  No ODE authority is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as Nonlinear
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityLookupExactRound71Exact as Lookup

CanonicalPositiveTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E) →
  Fixed.CanonicalRealityState F (Fixed.cutoff geometry) → Set r
CanonicalPositiveTransverse {E = E} geometry state =
  ∀ mode →
  mode Cube.∈ Orbit.canonicalCutoffOrbitModes (Fixed.cutoff geometry) →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (Fixed.realityVelocity state mode)
  ≡ C3.complexZero _

canonicalModeNonzero :
  ∀ {N mode} →
  mode Cube.∈ Orbit.canonicalCutoffOrbitModes N →
  Z3.NonZeroMode mode
canonicalModeNonzero {N} {mode} member = record
  { notZero = λ zeroEquality →
      Orbit.canonicalCutoffExcludesZero N
        (subst
          (λ selected → selected Cube.∈ Orbit.canonicalCutoffOrbitModes N)
          (sym zeroEquality) member)
  }

viscousPartTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    mode →
  C3.bilinearDot3
      (C3.modeVector E mode)
      (Fixed.realityVelocity state mode)
    ≡ C3.complexZero F →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (C3.complex3Scale
      (Fixed.viscousScalar geometry mode)
      (Fixed.realityVelocity state mode))
  ≡ C3.complexZero F
viscousPartTransverse {F = F} {E = E} geometry state mode inputZero =
  trans
    (Scaling.bilinearDot3ScaleRight
      (Fixed.viscousScalar geometry mode)
      (C3.modeVector E mode)
      (Fixed.realityVelocity state mode))
    (trans
      (cong
        (C3.complexMultiply (Fixed.viscousScalar geometry mode))
        inputZero)
      (Field.complexMultiplyZeroRight (Fixed.viscousScalar geometry mode)))

rawCanonicalRHSAtTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    mode →
  Z3.NonZeroMode mode →
  C3.bilinearDot3
      (C3.modeVector E mode)
      (Fixed.realityVelocity state mode)
    ≡ C3.complexZero F →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (Fixed.rawCanonicalRHSAt geometry state mode)
  ≡ C3.complexZero F
rawCanonicalRHSAtTransverse {E = E} geometry state mode nonzero inputZero =
  Nonlinear.transverseAdd
    (C3.modeVector E mode)
    (C3.complex3Scale
      (Fixed.viscousScalar geometry mode)
      (Fixed.realityVelocity state mode))
    (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.projectedNonlinearity
      (Fixed.fixedAuditSystem geometry state) mode)
    (viscousPartTransverse geometry state mode inputZero)
    (Nonlinear.projectedNonlinearityTransverseExact
      (Fixed.fixedAuditSystem geometry state) mode nonzero)

mappedRHSMember :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    {mode source} →
  mode Cube.∈ source →
  Fixed.canonical-mode-value mode (Fixed.rawCanonicalRHSAt geometry state mode)
    Cube.∈ Fixed.mapCanonicalRHS geometry source state
mappedRHSMember geometry state (Cube.here refl) = Cube.here refl
mappedRHSMember geometry state (Cube.there member) =
  Cube.there (mappedRHSMember geometry state member)

vectorFieldPositiveVelocityExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry))
    mode →
  (member : mode Cube.∈ Orbit.canonicalCutoffOrbitModes (Fixed.cutoff geometry)) →
  Fixed.realityVelocity
      (Fixed.fixedCanonicalRealityVectorField geometry state) mode
  ≡ Fixed.rawCanonicalRHSAt geometry state mode
vectorFieldPositiveVelocityExact geometry state mode member =
  Lookup.realityVelocityPositiveExact
    (Fixed.fixedCanonicalRealityVectorField geometry state)
    (Fixed.canonical-mode-value mode (Fixed.rawCanonicalRHSAt geometry state mode))
    (mappedRHSMember geometry state member)

fixedCanonicalVectorFieldPreservesTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : Fixed.FixedCanonicalGeometry F E)
    (state : Fixed.CanonicalRealityState F (Fixed.cutoff geometry)) →
  CanonicalPositiveTransverse geometry state →
  CanonicalPositiveTransverse geometry
    (Fixed.fixedCanonicalRealityVectorField geometry state)
fixedCanonicalVectorFieldPreservesTransverse {F = F} {E = E}
    geometry state inputTransverse mode member =
  trans
    (cong
      (C3.bilinearDot3 (C3.modeVector E mode))
      (vectorFieldPositiveVelocityExact geometry state mode member))
    (rawCanonicalRHSAtTransverse
      geometry state mode
      (canonicalModeNonzero member)
      (inputTransverse mode member))

round71FixedCanonicalTransverseSubspaceInvariant : Bool
round71FixedCanonicalTransverseSubspaceInvariant = true

round71FixedCanonicalTransverseSubspaceInvariantIsTrue :
  round71FixedCanonicalTransverseSubspaceInvariant ≡ true
round71FixedCanonicalTransverseSubspaceInvariantIsTrue = refl
