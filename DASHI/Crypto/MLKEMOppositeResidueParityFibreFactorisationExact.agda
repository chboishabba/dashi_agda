module DASHI.Crypto.MLKEMOppositeResidueParityFibreFactorisationExact where

------------------------------------------------------------------------
-- ML-KEM / FIPS-203: OPPOSITE-RESIDUE FIBRE FACTORISATION
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Discovery context
-- -----------------
-- The source-faithful CBD block probe finds a reproducible conditioned-list
-- reduction for actual opposite FIPS residue pairs (gamma_1 = -gamma_0 and
-- gamma_3 = -gamma_2) relative to seeded generic field-point controls.
--
-- The preceding decomposition theorem proves that the sum/difference of the
-- two observations isolates even- and odd-exponent sectors.  This module
-- sharpens that statement to an exact fibre theorem: whenever doubling is
-- injective, two Poly8 values have the same opposite-residue observation pair
-- iff they have the same even sector and the same odd sector.
--
-- Thus the special FIPS pair does not merely have a suggestive symmetry: its
-- raw observation fibre literally factors through the parity-sector quotient.
-- This is an attack-discovery structural theorem, not a whole-key attack claim.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym)
open import Relation.Binary.PropositionalEquality.≡-Reasoning

import DASHI.Crypto.MLKEMOppositeResidueParityDecompositionExact as Opp

record DoubleInjective {c ℓ : Level} (R : CommutativeRing c ℓ) : Set (c ⊔ ℓ) where
  open CommutativeRing R renaming (Carrier to F)
  field
    doubleInjective :
      (x y : F) →
      Opp.twoTimes R x ≡ Opp.twoTimes R y →
      x ≡ y

open DoubleInjective public

module _ {c ℓ : Level} (R : CommutativeRing c ℓ) where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _+_ to _⊕_
      ; -_ to neg
      )

  sameOppositePairForcesSameEven :
    (injective2 : DoubleInjective R) →
    (a : F) →
    (left right : Opp.Poly8 R) →
    Opp.evalPlus R a left ≡ Opp.evalPlus R a right →
    Opp.evalMinus R a left ≡ Opp.evalMinus R a right →
    Opp.evenPart R a left ≡ Opp.evenPart R a right
  sameOppositePairForcesSameEven injective2 a left right plusSame minusSame =
    doubleInjective injective2
      (Opp.evenPart R a left)
      (Opp.evenPart R a right)
      doubledSame
    where
    doubledSame :
      Opp.twoTimes R (Opp.evenPart R a left) ≡
      Opp.twoTimes R (Opp.evenPart R a right)
    doubledSame =
      begin
        Opp.twoTimes R (Opp.evenPart R a left)
      ≡⟨ sym (Opp.oppositeResidueSumSelectsEven R a left) ⟩
        Opp.evalPlus R a left ⊕ Opp.evalMinus R a left
      ≡⟨ cong₂ _⊕_ plusSame minusSame ⟩
        Opp.evalPlus R a right ⊕ Opp.evalMinus R a right
      ≡⟨ Opp.oppositeResidueSumSelectsEven R a right ⟩
        Opp.twoTimes R (Opp.evenPart R a right)
      ∎

  sameOppositePairForcesSameOdd :
    (injective2 : DoubleInjective R) →
    (a : F) →
    (left right : Opp.Poly8 R) →
    Opp.evalPlus R a left ≡ Opp.evalPlus R a right →
    Opp.evalMinus R a left ≡ Opp.evalMinus R a right →
    Opp.oddPart R a left ≡ Opp.oddPart R a right
  sameOppositePairForcesSameOdd injective2 a left right plusSame minusSame =
    doubleInjective injective2
      (Opp.oddPart R a left)
      (Opp.oddPart R a right)
      doubledSame
    where
    doubledSame :
      Opp.twoTimes R (Opp.oddPart R a left) ≡
      Opp.twoTimes R (Opp.oddPart R a right)
    doubledSame =
      begin
        Opp.twoTimes R (Opp.oddPart R a left)
      ≡⟨ sym (Opp.oppositeResidueDifferenceSelectsOdd R a left) ⟩
        Opp.evalPlus R a left ⊕ neg (Opp.evalMinus R a left)
      ≡⟨ cong₂ _⊕_ plusSame (cong neg minusSame) ⟩
        Opp.evalPlus R a right ⊕ neg (Opp.evalMinus R a right)
      ≡⟨ Opp.oppositeResidueDifferenceSelectsOdd R a right ⟩
        Opp.twoTimes R (Opp.oddPart R a right)
      ∎

  sameOppositePairForcesSameParitySectors :
    (injective2 : DoubleInjective R) →
    (a : F) →
    (left right : Opp.Poly8 R) →
    Opp.evalPlus R a left ≡ Opp.evalPlus R a right →
    Opp.evalMinus R a left ≡ Opp.evalMinus R a right →
    (Opp.evenPart R a left ≡ Opp.evenPart R a right) ×
    (Opp.oddPart R a left ≡ Opp.oddPart R a right)
  sameOppositePairForcesSameParitySectors injective2 a left right plusSame minusSame =
    sameOppositePairForcesSameEven injective2 a left right plusSame minusSame ,
    sameOppositePairForcesSameOdd injective2 a left right plusSame minusSame

  sameParitySectorsForceSameOppositePair :
    (a : F) →
    (left right : Opp.Poly8 R) →
    Opp.evenPart R a left ≡ Opp.evenPart R a right →
    Opp.oddPart R a left ≡ Opp.oddPart R a right →
    (Opp.evalPlus R a left ≡ Opp.evalPlus R a right) ×
    (Opp.evalMinus R a left ≡ Opp.evalMinus R a right)
  sameParitySectorsForceSameOppositePair a left right evenSame oddSame =
    cong₂ _⊕_ evenSame oddSame ,
    cong₂ _⊕_ evenSame (cong neg oddSame)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- For F_3329, doubling is injective because 2 is nonzero/invertible; that
-- concrete field producer is still separate.  Likewise this theorem explains
-- the exact parity-sector fibre geometry but does not identify the measured
-- conditioned-list ratio with a whole-key recovery speedup.
--
-- The current discovery script compares the opposite FIPS pairs against seeded
-- generic field-point controls.  At m=8 the observed conditioned-list means are
-- roughly half the control mean in the deterministic benchmark.  Those measured
-- numbers remain computational regressions rather than kernel theorems.
------------------------------------------------------------------------
