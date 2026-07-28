module DASHI.Physics.Closure.NSTriadKNComplex3RestrictedUniquenessInputs where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; DASHI repository contributors.
-- Title: "Algebraic inputs for restricted transverse uniqueness on the exact
-- Stage-3 C3 carrier".
-- Venue/year: Handbook of Mathematical Fluid Dynamics, Volume 3, 2005;
-- DASHI formal development, 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier-Stokes
-- Equations"; the finite-dimensional reduction is repository-original.
-- Uses: transverse closure under subtraction, Hermitian subtraction in the
-- tested slot, Re <d,d> = ||d||^2, and additive inverse cancellation.
-- Relationship: proves that equality against the difference test forces the
-- squared norm of the difference to vanish.  Only ordered positive-definite
-- separation ||d||^2 = 0 -> d = 0 remains for concrete restricted uniqueness.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Euclidean
import DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing as SelfPairing
import DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference as Difference

realOfComplexSubtract :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.real (C3.complexSubtract a b)
  ≡ C3.add F (C3.real a) (C3.negate F (C3.real b))
realOfComplexSubtract (C3.complex ar ai) (C3.complex br bi) = refl

realSubtractEqualIsZero :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.real a ≡ C3.real b →
  C3.real (C3.complexSubtract a b) ≡ C3.zero F
realSubtractEqualIsZero {F = F} a b equal =
  trans
    (realOfComplexSubtract a b)
    (trans
      (Algebra.cong₂ (C3.add F) equal refl)
      (Algebra.realAddInverseRight F (C3.real b)))

differenceSelfTestForcesZeroNormSquared :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.real
    (C3.hermitianPairing3 (C3.complex3Subtract u v) u)
  ≡
  C3.real
    (C3.hermitianPairing3 (C3.complex3Subtract u v) v) →
  Euclidean.complex3NormSquared (C3.complex3Subtract u v)
  ≡ C3.zero F
differenceSelfTestForcesZeroNormSquared {F = F} u v sameTest =
  trans
    (sym
      (SelfPairing.complex3SelfPairingRealPartIsNormSquared
        (C3.complex3Subtract u v)))
    (trans
      (cong C3.real
        (Additive.hermitianPairingSubtractRight
          (C3.complex3Subtract u v) u v))
      (realSubtractEqualIsZero
        (C3.hermitianPairing3 (C3.complex3Subtract u v) u)
        (C3.hermitianPairing3 (C3.complex3Subtract u v) v)
        sameTest))

complex3RestrictedUniquenessAlgebraClosed : Bool
complex3RestrictedUniquenessAlgebraClosed = true

complex3RestrictedUniquenessAlgebraClosedIsTrue :
  complex3RestrictedUniquenessAlgebraClosed ≡ true
complex3RestrictedUniquenessAlgebraClosedIsTrue = refl

zeroNormSquaredSeparatesComplex3StillRequired : Bool
zeroNormSquaredSeparatesComplex3StillRequired = true

zeroNormSquaredSeparatesComplex3StillRequiredIsTrue :
  zeroNormSquaredSeparatesComplex3StillRequired ≡ true
zeroNormSquaredSeparatesComplex3StillRequiredIsTrue = refl
