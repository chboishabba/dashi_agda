module DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Reconstruct finite-group class characters from the multiplicities in the
-- octahedral and icosahedral control spectra, and verify the critical control
-- rows against the restricted SO(3) characters exactly.
--
-- Certified O ~= S4 rows: j=2 (dimension 5), j=4 (dimension 9),
--                         j=26 (dimension 53).
-- Certified I ~= A5 rows: j=3 (dimension 7), j=4 (dimension 9),
--                         j=33 (dimension 67).
--
-- The A5 fifth-turn calculation uses exact Z[phi] pairs a+b*phi; there is no
-- floating approximation in the proof surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed

scaleInt : Nat → ℤ → ℤ
scaleInt 0 value = + 0
scaleInt (suc n) value = value +ℤ scaleInt n value

octahedralBranchingCharacter :
  Oct.OctahedralSpectrum → Oct.OctahedralClass → ℤ
octahedralBranchingCharacter spectrum class =
  scaleInt (Oct.multiplicityA1 spectrum) (Oct.irrepCharacter Oct.A1 class)
  +ℤ scaleInt (Oct.multiplicityA2 spectrum) (Oct.irrepCharacter Oct.A2 class)
  +ℤ scaleInt (Oct.multiplicityE spectrum) (Oct.irrepCharacter Oct.E class)
  +ℤ scaleInt (Oct.multiplicityT1 spectrum) (Oct.irrepCharacter Oct.T1 class)
  +ℤ scaleInt (Oct.multiplicityT2 spectrum) (Oct.irrepCharacter Oct.T2 class)

quarterTurnCharacter : Nat → ℤ
quarterTurnCharacter 0 = + 1
quarterTurnCharacter (suc 0) = + 1
quarterTurnCharacter (suc (suc 0)) = -[1+ 0 ]
quarterTurnCharacter (suc (suc (suc 0))) = -[1+ 0 ]
quarterTurnCharacter (suc (suc (suc (suc n)))) = quarterTurnCharacter n

restrictedOctahedralCharacter :
  Spin.AngularMomentum0To35 → Oct.OctahedralClass → ℤ
restrictedOctahedralCharacter j Oct.identityClass = + (Spin.jDimension j)
restrictedOctahedralCharacter j Oct.edgeHalfTurnClass =
  Fixed.halfTurnCharacter (Spin.jNat j)
restrictedOctahedralCharacter j Oct.faceHalfTurnClass =
  Fixed.halfTurnCharacter (Spin.jNat j)
restrictedOctahedralCharacter j Oct.thirdTurnClass =
  Fixed.thirdTurnCharacter (Spin.jNat j)
restrictedOctahedralCharacter j Oct.quarterTurnClass =
  quarterTurnCharacter (Spin.jNat j)

j2OctahedralCharacterExact :
  (class : Oct.OctahedralClass) →
  octahedralBranchingCharacter (Oct.branchingSpectrum Spin.j2) class
  ≡ restrictedOctahedralCharacter Spin.j2 class
j2OctahedralCharacterExact Oct.identityClass = refl
j2OctahedralCharacterExact Oct.edgeHalfTurnClass = refl
j2OctahedralCharacterExact Oct.faceHalfTurnClass = refl
j2OctahedralCharacterExact Oct.thirdTurnClass = refl
j2OctahedralCharacterExact Oct.quarterTurnClass = refl

j4OctahedralCharacterExact :
  (class : Oct.OctahedralClass) →
  octahedralBranchingCharacter (Oct.branchingSpectrum Spin.j4) class
  ≡ restrictedOctahedralCharacter Spin.j4 class
j4OctahedralCharacterExact Oct.identityClass = refl
j4OctahedralCharacterExact Oct.edgeHalfTurnClass = refl
j4OctahedralCharacterExact Oct.faceHalfTurnClass = refl
j4OctahedralCharacterExact Oct.thirdTurnClass = refl
j4OctahedralCharacterExact Oct.quarterTurnClass = refl

j26OctahedralCharacterExact :
  (class : Oct.OctahedralClass) →
  octahedralBranchingCharacter (Oct.branchingSpectrum Spin.j26) class
  ≡ restrictedOctahedralCharacter Spin.j26 class
j26OctahedralCharacterExact Oct.identityClass = refl
j26OctahedralCharacterExact Oct.edgeHalfTurnClass = refl
j26OctahedralCharacterExact Oct.faceHalfTurnClass = refl
j26OctahedralCharacterExact Oct.thirdTurnClass = refl
j26OctahedralCharacterExact Oct.quarterTurnClass = refl

------------------------------------------------------------------------
-- A5 character arithmetic in Z[phi].
------------------------------------------------------------------------

addPhi : Ico.PhiInt → Ico.PhiInt → Ico.PhiInt
addPhi left right =
  Ico.phi-int
    (Ico.rationalPart left +ℤ Ico.rationalPart right)
    (Ico.goldenPart left +ℤ Ico.goldenPart right)

zeroPhi : Ico.PhiInt
zeroPhi = Ico.phi-int (+ 0) (+ 0)

scalePhi : Nat → Ico.PhiInt → Ico.PhiInt
scalePhi 0 value = zeroPhi
scalePhi (suc n) value = addPhi value (scalePhi n value)

integerPhi : ℤ → Ico.PhiInt
integerPhi value = Ico.phi-int value (+ 0)

icosahedralBranchingCharacter :
  Ico.IcosahedralSpectrum → Ico.IcosahedralClass → Ico.PhiInt
icosahedralBranchingCharacter spectrum class =
  addPhi
    (scalePhi (Ico.multiplicityI1 spectrum) (Ico.irrepCharacter Ico.I1 class))
    (addPhi
      (scalePhi (Ico.multiplicityI3 spectrum) (Ico.irrepCharacter Ico.I3 class))
      (addPhi
        (scalePhi
          (Ico.multiplicityI3Prime spectrum)
          (Ico.irrepCharacter Ico.I3Prime class))
        (addPhi
          (scalePhi (Ico.multiplicityI4 spectrum) (Ico.irrepCharacter Ico.I4 class))
          (scalePhi (Ico.multiplicityI5 spectrum) (Ico.irrepCharacter Ico.I5 class)))))

fifthTurnCharacter : Nat → Ico.PhiInt
fifthTurnCharacter 0 = Ico.phi-int (+ 1) (+ 0)
fifthTurnCharacter (suc 0) = Ico.phi
fifthTurnCharacter (suc (suc 0)) = zeroPhi
fifthTurnCharacter (suc (suc (suc 0))) = Ico.phi-int (+ 0) (-[1+ 0 ])
fifthTurnCharacter (suc (suc (suc (suc 0)))) = Ico.phi-int (-[1+ 0 ]) (+ 0)
fifthTurnCharacter (suc (suc (suc (suc (suc n))))) = fifthTurnCharacter n

fifthTurnSquaredCharacter : Nat → Ico.PhiInt
fifthTurnSquaredCharacter 0 = Ico.phi-int (+ 1) (+ 0)
fifthTurnSquaredCharacter (suc 0) = Ico.goldenConjugate
fifthTurnSquaredCharacter (suc (suc 0)) = zeroPhi
fifthTurnSquaredCharacter (suc (suc (suc 0))) = Ico.phi-int (-[1+ 0 ]) (+ 1)
fifthTurnSquaredCharacter (suc (suc (suc (suc 0)))) = Ico.phi-int (-[1+ 0 ]) (+ 0)
fifthTurnSquaredCharacter (suc (suc (suc (suc (suc n))))) =
  fifthTurnSquaredCharacter n

restrictedIcosahedralCharacter :
  Spin.AngularMomentum0To35 → Ico.IcosahedralClass → Ico.PhiInt
restrictedIcosahedralCharacter j Ico.identityClass =
  Ico.phi-int (+ (Spin.jDimension j)) (+ 0)
restrictedIcosahedralCharacter j Ico.halfTurnClass =
  integerPhi (Fixed.halfTurnCharacter (Spin.jNat j))
restrictedIcosahedralCharacter j Ico.thirdTurnClass =
  integerPhi (Fixed.thirdTurnCharacter (Spin.jNat j))
restrictedIcosahedralCharacter j Ico.fifthTurnClass =
  fifthTurnCharacter (Spin.jNat j)
restrictedIcosahedralCharacter j Ico.fifthTurnSquaredClass =
  fifthTurnSquaredCharacter (Spin.jNat j)

j3IcosahedralCharacterExact :
  (class : Ico.IcosahedralClass) →
  icosahedralBranchingCharacter (Ico.branchingSpectrum Spin.j3) class
  ≡ restrictedIcosahedralCharacter Spin.j3 class
j3IcosahedralCharacterExact Ico.identityClass = refl
j3IcosahedralCharacterExact Ico.halfTurnClass = refl
j3IcosahedralCharacterExact Ico.thirdTurnClass = refl
j3IcosahedralCharacterExact Ico.fifthTurnClass = refl
j3IcosahedralCharacterExact Ico.fifthTurnSquaredClass = refl

j4IcosahedralCharacterExact :
  (class : Ico.IcosahedralClass) →
  icosahedralBranchingCharacter (Ico.branchingSpectrum Spin.j4) class
  ≡ restrictedIcosahedralCharacter Spin.j4 class
j4IcosahedralCharacterExact Ico.identityClass = refl
j4IcosahedralCharacterExact Ico.halfTurnClass = refl
j4IcosahedralCharacterExact Ico.thirdTurnClass = refl
j4IcosahedralCharacterExact Ico.fifthTurnClass = refl
j4IcosahedralCharacterExact Ico.fifthTurnSquaredClass = refl

j33IcosahedralCharacterExact :
  (class : Ico.IcosahedralClass) →
  icosahedralBranchingCharacter (Ico.branchingSpectrum Spin.j33) class
  ≡ restrictedIcosahedralCharacter Spin.j33 class
j33IcosahedralCharacterExact Ico.identityClass = refl
j33IcosahedralCharacterExact Ico.halfTurnClass = refl
j33IcosahedralCharacterExact Ico.thirdTurnClass = refl
j33IcosahedralCharacterExact Ico.fifthTurnClass = refl
j33IcosahedralCharacterExact Ico.fifthTurnSquaredClass = refl

record CriticalCharacterVerificationBoundary : Set where
  field
    octahedralControlRowsCharacterCertified : Bool
    octahedralControlRowsCharacterCertifiedIsTrue :
      octahedralControlRowsCharacterCertified ≡ true
    icosahedralControlRowsCharacterCertified : Bool
    icosahedralControlRowsCharacterCertifiedIsTrue :
      icosahedralControlRowsCharacterCertified ≡ true
    allTableRowsClaimedCharacterCertifiedHere : Bool
    allTableRowsClaimedCharacterCertifiedHereIsFalse :
      allTableRowsClaimedCharacterCertifiedHere ≡ false

canonicalCriticalCharacterVerificationBoundary :
  CriticalCharacterVerificationBoundary
canonicalCriticalCharacterVerificationBoundary =
  record
    { octahedralControlRowsCharacterCertified = true
    ; octahedralControlRowsCharacterCertifiedIsTrue = refl
    ; icosahedralControlRowsCharacterCertified = true
    ; icosahedralControlRowsCharacterCertifiedIsTrue = refl
    ; allTableRowsClaimedCharacterCertifiedHere = false
    ; allTableRowsClaimedCharacterCertifiedHereIsFalse = refl
    }
