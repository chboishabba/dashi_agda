{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRationalS3DegreeThirteenInvariantCertificateExact where

------------------------------------------------------------------------
-- Compact degree-13 positive rational cubature MOMENT certificate.
--
-- Nine signed-permutation orbit representatives are actual ORIGINAL
-- RationalUnitQuaternion values, each with a proved exact unit norm.
-- The 9 rational total masses are the previously verified 1000-node
-- cubature. Their invariant moments are checked without 2380
-- separately written Agda monomial equalities.
--
-- IMPORTANT: this module does not yet prove that Reynolds averaging
-- over the complete signed-permutation orbit is exact in Agda.
-- The separate complete 2380-monomial exact checker and the SymPy
-- symmetric polynomial reduction validate this mathematical step.
-- The group-orbit enumeration and invariant-basis spanning proof are
-- still kernel obligations. Do not claim full degree-13 Agda cubature.
--
-- Attribution: Pizzetti/Folland, rational design moment owners,
-- original DASHI rational SU(2) carrier, Bishop, Wilson/Balaban.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact
  as Original

record Orbit : Set where
  constructor orbit
  field
    representative : Original.RationalUnitQuaternion
    mass : ℚ
open Orbit public

-- The record constructor enforces ORIGINAL rational unit norm; these
-- witnesses are plain rational polynomial identities.
make : (a b c d : ℚ) (w : ℚ) →
       a * a + b * b + c * c + d * d ≡ 1ℚ → Orbit
make a b c d w norm =
  orbit (Original.rationalUnitQuaternion a b c d norm) w

axis half third fiveA fiveB sevenB sevenC nine ten : Orbit
axis = make (+ 1 / 1) 0ℚ 0ℚ 0ℚ
  (+ 1232693496262979 / 42382499047004160) (ℚRing.solve [])
half = make (+ 1 / 2) (+ 1 / 2) (+ 1 / 2) (+ 1 / 2)
  (+ 154914431412869 / 3862988194388400) (ℚRing.solve [])
third = make (+ 1 / 3) (+ 2 / 3) (+ 2 / 3) 0ℚ
  (+ 4035413081670039 / 22790040639815680) (ℚRing.solve [])
fiveA = make 0ℚ (+ 4 / 5) (+ 3 / 5) 0ℚ
  (+ 13445238508984375 / 237341994663223296) (ℚRing.solve [])
fiveB = make (+ 1 / 5) (+ 4 / 5) (+ 2 / 5) (+ 2 / 5)
  (+ 956994289818171875 / 6645575850570252288) (ℚRing.solve [])
sevenB = make (+ 1 / 7) (+ 4 / 7) (+ 4 / 7) (+ 4 / 7)
  (+ 237100934228276867 / 3390599923760332800) (ℚRing.solve [])
sevenC = make (+ 2 / 7) (+ 5 / 7) (+ 4 / 7) (+ 2 / 7)
  (+ 126941819652170803 / 678119984752066560) (ℚRing.solve [])
nine = make (+ 1 / 9) (+ 8 / 9) (+ 4 / 9) 0ℚ
  (+ 4944993667603677 / 45580081279631360) (ℚRing.solve [])
ten = make (+ 1 / 10) (+ 9 / 10) (+ 3 / 10) (+ 3 / 10)
  (+ 608335914359375 / 3244910083286256) (ℚRing.solve [])

allOrbits : List Orbit
allOrbits =
  axis ∷ half ∷ third ∷ fiveA ∷ fiveB ∷ sevenB ∷ sevenC ∷
  nine ∷ ten ∷ []

square : ℚ → ℚ
square x = x * x

-- Symmetric invariants of y_i = q_i^2. They are invariant under
-- coordinate sign changes and permutations of the ORIGINAL quaternion.
invariant2 invariant3 invariant4 : Original.RationalUnitQuaternion → ℚ
invariant2 q =
  let a = square (Original.realPart q)
      b = square (Original.imagI q)
      c = square (Original.imagJ q)
      d = square (Original.imagK q)
  in a * b + a * c + a * d + b * c + b * d + c * d

invariant3 q =
  let a = square (Original.realPart q)
      b = square (Original.imagI q)
      c = square (Original.imagJ q)
      d = square (Original.imagK q)
  in a * b * c + a * b * d + a * c * d + b * c * d

invariant4 q =
  let a = square (Original.realPart q)
      b = square (Original.imagI q)
      c = square (Original.imagJ q)
      d = square (Original.imagK q)
  in a * b * c * d

weighted : (Original.RationalUnitQuaternion → ℚ) → List Orbit → ℚ
weighted f [] = 0ℚ
weighted f (o ∷ os) =
  mass o * f (representative o) + weighted f os

-- e1 = q0²+q1²+q2²+q3² = 1 on every original unit quaternion.
-- Degree<=13 signed-symmetric sphere polynomials have basis
-- 1,e2,e3,e4,e2²,e2e3,e2³,e3²,e2e4.
-- The following 9 equations are genuine closed rational computations,
-- not free external moment fields.

momentOne : weighted (λ _ → 1ℚ) allOrbits ≡ 1ℚ
momentOne = refl

momentE2 :
  weighted invariant2 allOrbits ≡ (+ 1 / 4)
momentE2 = refl

momentE3 :
  weighted invariant3 allOrbits ≡ (+ 1 / 48)
momentE3 = refl

momentE4 :
  weighted invariant4 allOrbits ≡ (+ 1 / 1920)
momentE4 = refl

momentE2Squared :
  weighted (λ q → square (invariant2 q)) allOrbits
    ≡ (+ 11 / 160)
momentE2Squared = refl

momentE2E3 :
  weighted (λ q → invariant2 q * invariant3 q) allOrbits
    ≡ (+ 1 / 160)
momentE2E3 = refl

momentE2Cubed :
  weighted (λ q → square (invariant2 q) * invariant2 q) allOrbits
    ≡ (+ 89 / 4480)
momentE2Cubed = refl

momentE3Squared :
  weighted (λ q → square (invariant3 q)) allOrbits
    ≡ (+ 3 / 4480)
momentE3Squared = refl

momentE2E4 :
  weighted (λ q → invariant2 q * invariant4 q) allOrbits
    ≡ (+ 3 / 17920)
momentE2E4 = refl
