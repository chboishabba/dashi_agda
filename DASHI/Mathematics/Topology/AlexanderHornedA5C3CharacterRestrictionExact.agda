module DASHI.Mathematics.Topology.AlexanderHornedA5C3CharacterRestrictionExact where

------------------------------------------------------------------------
-- SOURCE: existing icosahedral A5 / C3 character-restriction tables
--
-- Primary mathematical authorities: Serre; Fulton and Harris.
-- Exact local donors:
--   Foundations.IcosahedralSO3RestrictionJ0To35Exact
--   Foundations.PolyhedralFiniteRestrictionInstancesExact
--   Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact
--   Foundations.FiniteRepresentationRestrictionCore
--
-- The five irreducible A5 dimensions are 1,3,3',4,5. Their
-- character values on a three-cycle are 1,0,0,1,-1.
-- Restriction to C3 therefore has fixed-space dimensions
-- 1,1,1,2,1. The A5 REGULAR representation has exactly
--   sum(dim_i * fixed_i) = 20
-- fixed coordinates under an internal C3 generator. Its total
-- dimension is 60. This matches the combinatorial decomposition
-- of C[A5] into twenty 3-element C3 orbits.
--
-- The 3 copies x outer C3 give C3_int x C3_ext, 20 independent
-- 9-element orbits, hence 20 copies of the regular representation
-- of C3 x C3, and nine cyclotomic characters each of multiplicity
-- 20. The 9-orbit count is audited by the finite permutation script;
-- this file proves the irrep-dimension combinatorial reconciliation.
--
-- This is NOT a homomorphism A5 -> C3; it is restriction along the
-- embedded C3 <= A5. It does not identify any Monster module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (+_; -[1+_])

import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as A5
import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.PolyhedralFiniteRestrictionInstancesExact as Poly
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

-- The values are not reconstructed from an untrusted dimension 60:
-- every class value is read from the existing precise A5 character
-- table and verified as a definitional equality.
thirdTurnTrivial : A5.irrepCharacter A5.I1 A5.thirdTurnClass
  ≡ A5.phiOne
thirdTurnTrivial = refl

thirdTurnThree : A5.irrepCharacter A5.I3 A5.thirdTurnClass
  ≡ A5.phiZero
thirdTurnThree = refl

thirdTurnThreePrime : A5.irrepCharacter A5.I3Prime A5.thirdTurnClass
  ≡ A5.phiZero
thirdTurnThreePrime = refl

thirdTurnFour : A5.irrepCharacter A5.I4 A5.thirdTurnClass
  ≡ A5.phiOne
thirdTurnFour = refl

thirdTurnFive : A5.irrepCharacter A5.I5 A5.thirdTurnClass
  ≡ A5.phi-int (-[1+ 0 ]) (+ 0)
thirdTurnFive = refl

c3FixedInIrrep : A5.IcosahedralIrrep → Nat
c3FixedInIrrep A5.I1 = 1
c3FixedInIrrep A5.I3 = 1
c3FixedInIrrep A5.I3Prime = 1
c3FixedInIrrep A5.I4 = 2
c3FixedInIrrep A5.I5 = 1

a5RegularDimension : Nat
a5RegularDimension =
  Core.sumWeighted A5.allIcosahedralIrreps
    A5.icosahedralIrrepDimension
    A5.icosahedralIrrepDimension

a5RegularDimensionIs60 : a5RegularDimension ≡ 60
a5RegularDimensionIs60 = refl

a5RegularC3FixedDimension : Nat
a5RegularC3FixedDimension =
  Core.sumWeighted A5.allIcosahedralIrreps
    A5.icosahedralIrrepDimension c3FixedInIrrep

a5RegularC3FixedDimensionIs20 :
  a5RegularC3FixedDimension ≡ 20
a5RegularC3FixedDimensionIs20 = refl

-- Exact links to the existing J0..35 C3 fixed-space scanner.
a5C3AgreesWithOldAxialProbe :
  ∀ j →
  Poly.icosahedralFixedDimension j Poly.icosahedralC3
    ≡ Fixed.fixedDimension j Fixed.C3Probe
a5C3AgreesWithOldAxialProbe j = refl

j3FixedDimensionReused :
  Poly.icosahedralFixedDimension Spin.j3 Poly.icosahedralC3 ≡ 3
j3FixedDimensionReused = refl

j35FixedDimensionReused :
  Poly.icosahedralFixedDimension Spin.j35 Poly.icosahedralC3 ≡ 23
j35FixedDimensionReused = refl

-- For Q[A5]^3 and C3_int x C3_ext, the 180-dimensional
-- permutation module decomposes as twenty orbits of size nine.
regularNineOrbitCount : Nat
regularNineOrbitCount = a5RegularC3FixedDimension

regularNineOrbitCountIs20 : regularNineOrbitCount ≡ 20
regularNineOrbitCountIs20 = a5RegularC3FixedDimensionIs20
