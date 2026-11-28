{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRationalS3DegreeFifteenInvariantCertificateExact where

-- Original rational SU2 eleven-orbit degree-15 design certificate.
-- Source reuses degree-13 original RationalUnitQuaternion and invariants.
-- The eleven equations below are exact rational source expressions.
-- A complete Reynolds/orbit enumeration proof and Agda kernel acceptance
-- remain separate; do not claim continuous Bishop Haar from this module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.YangMills.YMClayRationalS3DegreeThirteenInvariantCertificateExact as D13

orbit0 orbit1 orbit2 orbit3 orbit4 orbit5 orbit6 orbit7 orbit8 orbit9 orbit10 : D13.Orbit
orbit0 = D13.make (+ 0 / 1) (+ 0 / 1) (+ 0 / 1) (+ 1 / 1)
  (+ 5885276409378220035186191 / 392284006841077089848524800) (ℚRing.solve [])
orbit1 = D13.make (+ 0 / 1) (+ 1 / 19) (+ 6 / 19) (+ 18 / 19)
  (+ 824693560522052736085185726477137 / 10149171824992346468561033625600000) (ℚRing.solve [])
orbit2 = D13.make (+ 0 / 1) (+ 1 / 17) (+ 12 / 17) (+ 12 / 17)
  (+ 35494525410219178540065425306543 / 730913368646465860733017620480000) (ℚRing.solve [])
orbit3 = D13.make (+ 0 / 1) (+ 2 / 11) (+ 6 / 11) (+ 9 / 11)
  (+ 471062302279446199657259685673 / 5242340818694393837066649600000) (ℚRing.solve [])
orbit4 = D13.make (+ 0 / 1) (+ 2 / 7) (+ 3 / 7) (+ 6 / 7)
  (+ 9885750716129338579831646703499 / 88768266690895158617151897600000) (ℚRing.solve [])
orbit5 = D13.make (+ 0 / 1) (+ 1 / 3) (+ 2 / 3) (+ 2 / 3)
  (+ 41184780746981187413434527 / 937511542031411182567424000) (ℚRing.solve [])
orbit6 = D13.make (+ 0 / 1) (+ 6 / 11) (+ 6 / 11) (+ 7 / 11)
  (+ 40400171940295056739147947380699 / 433937435931111457206986342400000) (ℚRing.solve [])
orbit7 = D13.make (+ 1 / 10) (+ 3 / 10) (+ 3 / 10) (+ 9 / 10)
  (+ 8757912318951982421875 / 80448868590455262566592) (ℚRing.solve [])
orbit8 = D13.make (+ 1 / 5) (+ 2 / 5) (+ 2 / 5) (+ 4 / 5)
  (+ 2313779947035071669921875 / 21696695687012658796560384) (ℚRing.solve [])
orbit9 = D13.make (+ 2 / 7) (+ 2 / 7) (+ 4 / 7) (+ 5 / 7)
  (+ 14522081148341910799643057 / 55348713487277190807552000) (ℚRing.solve [])
orbit10 = D13.make (+ 1 / 2) (+ 1 / 2) (+ 1 / 2) (+ 1 / 2)
  (+ 839369233794076039 / 21497746937751927360) (ℚRing.solve [])

allOrbits : List D13.Orbit
allOrbits = orbit0 ∷ orbit1 ∷ orbit2 ∷ orbit3 ∷ orbit4 ∷ orbit5 ∷ orbit6 ∷ orbit7 ∷ orbit8 ∷ orbit9 ∷ orbit10 ∷ []

e2 e3 e4 : D13.Orbit → ℚ
e2 o = D13.invariant2 (D13.representative o)
e3 o = D13.invariant3 (D13.representative o)
e4 o = D13.invariant4 (D13.representative o)

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = square x * x

momentMass : D13.weighted (λ _ → 1ℚ) allOrbits ≡ (+ 1 / 1)
momentMass = refl

momentE2 : D13.weighted (D13.invariant2) allOrbits ≡ (+ 1 / 4)
momentE2 = refl

momentE3 : D13.weighted (D13.invariant3) allOrbits ≡ (+ 1 / 48)
momentE3 = refl

momentE4 : D13.weighted (D13.invariant4) allOrbits ≡ (+ 1 / 1920)
momentE4 = refl

momentE2Squared : D13.weighted (λ q → square (D13.invariant2 q)) allOrbits ≡ (+ 11 / 160)
momentE2Squared = refl

momentE2E3 : D13.weighted (λ q → D13.invariant2 q * D13.invariant3 q) allOrbits ≡ (+ 1 / 160)
momentE2E3 = refl

momentE3Squared : D13.weighted (λ q → square (D13.invariant3 q)) allOrbits ≡ (+ 3 / 4480)
momentE3Squared = refl

momentE2E4 : D13.weighted (λ q → D13.invariant2 q * D13.invariant4 q) allOrbits ≡ (+ 3 / 17920)
momentE2E4 = refl

momentE2Cubed : D13.weighted (λ q → cube (D13.invariant2 q)) allOrbits ≡ (+ 89 / 4480)
momentE2Cubed = refl

momentE3E4 : D13.weighted (λ q → D13.invariant3 q * D13.invariant4 q) allOrbits ≡ (+ 3 / 143360)
momentE3E4 = refl

momentE2SquaredE3 : D13.weighted (λ q → square (D13.invariant2 q) * D13.invariant3 q) allOrbits ≡ (+ 69 / 35840)
momentE2SquaredE3 = refl

