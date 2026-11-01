module DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; DASHI repository contributors.
-- Title: "The exact C3 transverse Fourier fibre is closed under subtraction".
-- Venue/year: Handbook of Mathematical Fluid Dynamics, Volume 3, 2005;
-- DASHI formal development, 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0 for Marco Cannone,
-- "Harmonic Analysis Tools for Solving the Incompressible Navier-Stokes
-- Equations"; the coordinate proof is repository-original.
-- Uses: bilinear-dot additivity, the scalar minus-one action and the exact
-- transverse definition k dot u = 0.
-- Relationship: closes the linear-subspace step used by restricted-test
-- uniqueness.  Positive-definite zero-norm separation remains the only
-- ordered analytic input in that uniqueness argument.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

bilinearDot3NegateRight :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.complex3Negate v)
  ≡ C3.complexNegate (C3.bilinearDot3 u v)
bilinearDot3NegateRight {F = F} u v =
  trans
    (cong (C3.bilinearDot3 u)
      (sym (Additive.complex3ScaleMinusOne v)))
    (trans
      (Scaling.bilinearDot3ScaleRight (Additive.minusOne F) u v)
      (Additive.complexMultiplyMinusOneLeft (C3.bilinearDot3 u v)))

bilinearDot3SubtractRight :
  ∀ {r} {F : C3.RealField r} (u v w : C3.Complex3 F) →
  C3.bilinearDot3 u (C3.complex3Subtract v w)
  ≡ C3.complexSubtract
      (C3.bilinearDot3 u v)
      (C3.bilinearDot3 u w)
bilinearDot3SubtractRight u v w =
  trans
    (Algebra.bilinearDot3RightAdd u v (C3.complex3Negate w))
    (cong (C3.complexAdd (C3.bilinearDot3 u v))
      (bilinearDot3NegateRight u w))

transverseSubtract :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.Transverse E mode u →
  Helical.Transverse E mode v →
  Helical.Transverse E mode (C3.complex3Subtract u v)
transverseSubtract {F = F} E mode u v transverseU transverseV =
  trans
    (bilinearDot3SubtractRight (C3.modeVector E mode) u v)
    (trans
      (Algebra.cong₂ C3.complexSubtract transverseU transverseV)
      (Additive.complexSubtractSelf (C3.complexZero F)))

complex3TransverseDifferenceClosed : Bool
complex3TransverseDifferenceClosed = true

complex3TransverseDifferenceClosedIsTrue :
  complex3TransverseDifferenceClosed ≡ true
complex3TransverseDifferenceClosedIsTrue = refl
