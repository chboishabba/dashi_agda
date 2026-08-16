module DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Replace the earlier informal S2/S3-stabiliser reading by actual axial cyclic
-- fixed-space calculations.  For the SO(3) weight basis m=-j,...,j, a C_n
-- rotation fixes precisely the weights divisible by n, hence
--
--   dim(V_j^C_n) = 2*floor(j/n)+1.
--
-- The implementation avoids division by using exact n-step recurrences and
-- checks the C2/C3 character-average identities for every j=0..35.
--
-- IMPORTANT: the modular elliptic stabiliser of order three is C3.  The
-- repository's ternary coordinate permutation group is S3 of order six.
-- Those are distinct groups; S3 cannot be substituted for C3 by notation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin

data CyclicRotationProbe : Set where
  C2Probe C3Probe C4Probe C5Probe : CyclicRotationProbe

probeLabel : CyclicRotationProbe → String
probeLabel C2Probe = "C2 axial half-turn fixed subspace"
probeLabel C3Probe = "C3 axial third-turn fixed subspace"
probeLabel C4Probe = "C4 axial quarter-turn fixed subspace"
probeLabel C5Probe = "C5 axial fifth-turn fixed subspace"

fixedC2 : Nat → Nat
fixedC2 0 = 1
fixedC2 (suc 0) = 1
fixedC2 (suc (suc n)) = suc (suc (fixedC2 n))

fixedC3 : Nat → Nat
fixedC3 0 = 1
fixedC3 (suc 0) = 1
fixedC3 (suc (suc 0)) = 1
fixedC3 (suc (suc (suc n))) = suc (suc (fixedC3 n))

fixedC4 : Nat → Nat
fixedC4 0 = 1
fixedC4 (suc 0) = 1
fixedC4 (suc (suc 0)) = 1
fixedC4 (suc (suc (suc 0))) = 1
fixedC4 (suc (suc (suc (suc n)))) = suc (suc (fixedC4 n))

fixedC5 : Nat → Nat
fixedC5 0 = 1
fixedC5 (suc 0) = 1
fixedC5 (suc (suc 0)) = 1
fixedC5 (suc (suc (suc 0))) = 1
fixedC5 (suc (suc (suc (suc 0)))) = 1
fixedC5 (suc (suc (suc (suc (suc n))))) = suc (suc (fixedC5 n))

fixedDimension : Spin.AngularMomentum0To35 → CyclicRotationProbe → Nat
fixedDimension j C2Probe = fixedC2 (Spin.jNat j)
fixedDimension j C3Probe = fixedC3 (Spin.jNat j)
fixedDimension j C4Probe = fixedC4 (Spin.jNat j)
fixedDimension j C5Probe = fixedC5 (Spin.jNat j)

fixedSpaceSpectrum : Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum
fixedSpaceSpectrum j =
  Core.fixed-space-spectrum
    CyclicRotationProbe
    (fixedDimension j)
    probeLabel
    "exact C2/C3/C4/C5 axial fixed-space spectrum on j=0..35"

halfTurnCharacter : Nat → ℤ
halfTurnCharacter 0 = + 1
halfTurnCharacter (suc 0) = -[1+ 0 ]
halfTurnCharacter (suc (suc n)) = halfTurnCharacter n

thirdTurnCharacter : Nat → ℤ
thirdTurnCharacter 0 = + 1
thirdTurnCharacter (suc 0) = + 0
thirdTurnCharacter (suc (suc 0)) = -[1+ 0 ]
thirdTurnCharacter (suc (suc (suc n))) = thirdTurnCharacter n

c2CharacterAverageExact :
  (j : Spin.AngularMomentum0To35) →
  (+ 2) *ℤ (+ (fixedDimension j C2Probe))
  ≡ (+ (Spin.jDimension j)) +ℤ halfTurnCharacter (Spin.jNat j)
c2CharacterAverageExact Spin.j0 = refl
c2CharacterAverageExact Spin.j1 = refl
c2CharacterAverageExact Spin.j2 = refl
c2CharacterAverageExact Spin.j3 = refl
c2CharacterAverageExact Spin.j4 = refl
c2CharacterAverageExact Spin.j5 = refl
c2CharacterAverageExact Spin.j6 = refl
c2CharacterAverageExact Spin.j7 = refl
c2CharacterAverageExact Spin.j8 = refl
c2CharacterAverageExact Spin.j9 = refl
c2CharacterAverageExact Spin.j10 = refl
c2CharacterAverageExact Spin.j11 = refl
c2CharacterAverageExact Spin.j12 = refl
c2CharacterAverageExact Spin.j13 = refl
c2CharacterAverageExact Spin.j14 = refl
c2CharacterAverageExact Spin.j15 = refl
c2CharacterAverageExact Spin.j16 = refl
c2CharacterAverageExact Spin.j17 = refl
c2CharacterAverageExact Spin.j18 = refl
c2CharacterAverageExact Spin.j19 = refl
c2CharacterAverageExact Spin.j20 = refl
c2CharacterAverageExact Spin.j21 = refl
c2CharacterAverageExact Spin.j22 = refl
c2CharacterAverageExact Spin.j23 = refl
c2CharacterAverageExact Spin.j24 = refl
c2CharacterAverageExact Spin.j25 = refl
c2CharacterAverageExact Spin.j26 = refl
c2CharacterAverageExact Spin.j27 = refl
c2CharacterAverageExact Spin.j28 = refl
c2CharacterAverageExact Spin.j29 = refl
c2CharacterAverageExact Spin.j30 = refl
c2CharacterAverageExact Spin.j31 = refl
c2CharacterAverageExact Spin.j32 = refl
c2CharacterAverageExact Spin.j33 = refl
c2CharacterAverageExact Spin.j34 = refl
c2CharacterAverageExact Spin.j35 = refl

c3CharacterAverageExact :
  (j : Spin.AngularMomentum0To35) →
  (+ 3) *ℤ (+ (fixedDimension j C3Probe))
  ≡ (+ (Spin.jDimension j))
    +ℤ ((+ 2) *ℤ thirdTurnCharacter (Spin.jNat j))
c3CharacterAverageExact Spin.j0 = refl
c3CharacterAverageExact Spin.j1 = refl
c3CharacterAverageExact Spin.j2 = refl
c3CharacterAverageExact Spin.j3 = refl
c3CharacterAverageExact Spin.j4 = refl
c3CharacterAverageExact Spin.j5 = refl
c3CharacterAverageExact Spin.j6 = refl
c3CharacterAverageExact Spin.j7 = refl
c3CharacterAverageExact Spin.j8 = refl
c3CharacterAverageExact Spin.j9 = refl
c3CharacterAverageExact Spin.j10 = refl
c3CharacterAverageExact Spin.j11 = refl
c3CharacterAverageExact Spin.j12 = refl
c3CharacterAverageExact Spin.j13 = refl
c3CharacterAverageExact Spin.j14 = refl
c3CharacterAverageExact Spin.j15 = refl
c3CharacterAverageExact Spin.j16 = refl
c3CharacterAverageExact Spin.j17 = refl
c3CharacterAverageExact Spin.j18 = refl
c3CharacterAverageExact Spin.j19 = refl
c3CharacterAverageExact Spin.j20 = refl
c3CharacterAverageExact Spin.j21 = refl
c3CharacterAverageExact Spin.j22 = refl
c3CharacterAverageExact Spin.j23 = refl
c3CharacterAverageExact Spin.j24 = refl
c3CharacterAverageExact Spin.j25 = refl
c3CharacterAverageExact Spin.j26 = refl
c3CharacterAverageExact Spin.j27 = refl
c3CharacterAverageExact Spin.j28 = refl
c3CharacterAverageExact Spin.j29 = refl
c3CharacterAverageExact Spin.j30 = refl
c3CharacterAverageExact Spin.j31 = refl
c3CharacterAverageExact Spin.j32 = refl
c3CharacterAverageExact Spin.j33 = refl
c3CharacterAverageExact Spin.j34 = refl
c3CharacterAverageExact Spin.j35 = refl

orderC2 orderC3 orderTernaryS3 : Nat
orderC2 = 2
orderC3 = 3
orderTernaryS3 = 6

c3IsNotTernaryS3ByOrder : orderC3 ≡ orderTernaryS3 → ⊥
c3IsNotTernaryS3ByOrder ()

j3C2FixedDimension : fixedDimension Spin.j3 C2Probe ≡ 3
j3C2FixedDimension = refl

j3C3FixedDimension : fixedDimension Spin.j3 C3Probe ≡ 3
j3C3FixedDimension = refl

j4C3FixedDimension : fixedDimension Spin.j4 C3Probe ≡ 3
j4C3FixedDimension = refl

record PolyhedralFixedSpaceBoundary : Set where
  field
    cyclicFixedSpacesComputedWithoutOggFilter : Bool
    cyclicFixedSpacesComputedWithoutOggFilterIsTrue : cyclicFixedSpacesComputedWithoutOggFilter ≡ true
    c2CharacterAverageCheckedOnScan : Bool
    c2CharacterAverageCheckedOnScanIsTrue : c2CharacterAverageCheckedOnScan ≡ true
    c3CharacterAverageCheckedOnScan : Bool
    c3CharacterAverageCheckedOnScanIsTrue : c3CharacterAverageCheckedOnScan ≡ true
    c3IdentifiedWithS3 : Bool
    c3IdentifiedWithS3IsFalse : c3IdentifiedWithS3 ≡ false
    fixedSpaceSpectrumClaimedToSelectOggAlone : Bool
    fixedSpaceSpectrumClaimedToSelectOggAloneIsFalse : fixedSpaceSpectrumClaimedToSelectOggAlone ≡ false

canonicalPolyhedralFixedSpaceBoundary : PolyhedralFixedSpaceBoundary
canonicalPolyhedralFixedSpaceBoundary =
  record
    { cyclicFixedSpacesComputedWithoutOggFilter = true
    ; cyclicFixedSpacesComputedWithoutOggFilterIsTrue = refl
    ; c2CharacterAverageCheckedOnScan = true
    ; c2CharacterAverageCheckedOnScanIsTrue = refl
    ; c3CharacterAverageCheckedOnScan = true
    ; c3CharacterAverageCheckedOnScanIsTrue = refl
    ; c3IdentifiedWithS3 = false
    ; c3IdentifiedWithS3IsFalse = refl
    ; fixedSpaceSpectrumClaimedToSelectOggAlone = false
    ; fixedSpaceSpectrumClaimedToSelectOggAloneIsFalse = refl
    }
