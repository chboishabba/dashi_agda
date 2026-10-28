module DASHI.Statistics.ZipfFractionAddRationalBridgeExact where

------------------------------------------------------------------------
-- F13b: normalized-rational addition from the ORIGINAL raw FiniteFraction.
--
-- Mathematical roots:
-- - Classical equivalence of unreduced and reduced rational addition.
-- - Agda standard library Data.Rational.Properties: fromℚᵘ-cong,
--   fromℚᵘ-toℚᵘ, toℚᵘ-fromℚᵘ, toℚᵘ-homo-+.
-- - Data.Rational.Unnormalised.Properties: + cong, ≃ symmetry/transitivity.
--
-- Repository proof/source adaptation: Johl Brown-directed,
-- OpenAI ChatGPT assistance, 2026-10-28.
-- Existing original Agda/PNF, Zipf/Estoup, Mandelbrot/Hurwitz and
-- Ibrahim Monster 3B authors retain independent ownership.
--
-- This file contains an ACTUAL proof-term construction, not a 'paid'
-- Boolean and not a postulate. AGDA KERNEL TYPECHECK NOT EXECUTED.
-- The raw FiniteFraction carrier permits denominator 0: each quotient
-- below takes a constructor-level NONZERO witness explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base as ℤ using (+_)
open import Data.Nat.Base as Nat using (NonZero; nonZero)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Data.Rational.Base as ℚ
import Data.Rational.Properties as ℚP
import Data.Rational.Unnormalised.Base as ℚᵘ
import Data.Rational.Unnormalised.Properties as ℚᵘP

import DASHI.Core.FiniteUniformProbabilityNormalizationExact as Fraction
import DASHI.Statistics.ZipfFamilyFiniteExact as Zipf

-- No change to the existing source fraction type or addition operation.

validRawFraction :
  (a : Zipf.Fraction) →
  Nat.NonZero (Fraction.denominator a) →
  ℚᵘ.ℚᵘ
validRawFraction (Fraction.finiteFraction n zero) ()
validRawFraction (Fraction.finiteFraction n (suc d)) nz =
  ℚᵘ.mkℚᵘ (ℤ.+ n) d

validReducedFraction :
  (a : Zipf.Fraction) →
  Nat.NonZero (Fraction.denominator a) →
  ℚ.ℚ
validReducedFraction a nz =
  ℚ.normalize (Fraction.numerator a) (Fraction.denominator a) {{nz}}

-- The standard-library normalizer agrees definitionally with its
-- already-owned map from the unnormalised rational representation.

rawToReduced :
  (a : Zipf.Fraction)
  (nz : Nat.NonZero (Fraction.denominator a)) →
  ℚ.fromℚᵘ (validRawFraction a nz) ≡ validReducedFraction a nz
rawToReduced (Fraction.finiteFraction n zero) ()
rawToReduced (Fraction.finiteFraction n (suc d)) nz = refl

-- Proof object for the exact source addFraction. Both positive
-- denominators are required and the output proof uses the existing
-- Nat.m*n≢0 owner, rather than dividing by an unchecked Nat.

rawFractionAddPreserved :
  (a b : Zipf.Fraction) →
  (ha : Nat.NonZero (Fraction.denominator a)) →
  (hb : Nat.NonZero (Fraction.denominator b)) →
  validRawFraction (Zipf.addFraction a b)
    (NatP.m*n≢0 (Fraction.denominator a) (Fraction.denominator b)
      {{ha}} {{hb}})
  ≡ ℚᵘ._+_ (validRawFraction a ha) (validRawFraction b hb)
rawFractionAddPreserved (Fraction.finiteFraction n zero) b () hb
rawFractionAddPreserved (Fraction.finiteFraction n (suc d))
                        (Fraction.finiteFraction m zero) ha ()
rawFractionAddPreserved (Fraction.finiteFraction n (suc d))
                        (Fraction.finiteFraction m (suc e)) ha hb = refl

-- Lift the standard library's unnormalised equality to reduced
-- rational equality; DO NOT re-prove the original rational group laws.
-- This depends exclusively on published standard-library isomorphism
-- lemmas. In particular, ℚ.fromℚᵘ-cong consumes ℚᵘ equivalence,
-- not propositional equality between all unreduced representatives.

fromRawPreservesAddition :
  (x y : ℚᵘ.ℚᵘ) →
  ℚ.fromℚᵘ (ℚᵘ._+_ x y) ≡
    ℚ._+_ (ℚ.fromℚᵘ x) (ℚ.fromℚᵘ y)
fromRawPreservesAddition x y =
  trans
    (ℚP.fromℚᵘ-cong
      (ℚᵘP.≃-trans
        (ℚᵘP.+-cong
          (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ x))
          (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ y)))
        (ℚᵘP.≃-sym
          (ℚP.toℚᵘ-homo-+
            (ℚ.fromℚᵘ x) (ℚ.fromℚᵘ y)))))
    (ℚP.fromℚᵘ-toℚᵘ
      (ℚ._+_ (ℚ.fromℚᵘ x) (ℚ.fromℚᵘ y)))

-- F13b's single missing law, on its correct proof-carrying domain.
-- Every proof step is a term. Zero denominators have NO inhabitant.

positiveDenominatorAddHomomorphism :
  (a b : Zipf.Fraction) →
  (ha : Nat.NonZero (Fraction.denominator a)) →
  (hb : Nat.NonZero (Fraction.denominator b)) →
  validReducedFraction (Zipf.addFraction a b)
    (NatP.m*n≢0 (Fraction.denominator a) (Fraction.denominator b)
      {{ha}} {{hb}})
  ≡
  ℚ._+_ (validReducedFraction a ha) (validReducedFraction b hb)
positiveDenominatorAddHomomorphism a b ha hb =
  trans
    (sym (rawToReduced (Zipf.addFraction a b)
      (NatP.m*n≢0
        (Fraction.denominator a) (Fraction.denominator b)
        {{ha}} {{hb}})))
    (trans
      (cong ℚ.fromℚᵘ (rawFractionAddPreserved a b ha hb))
      (trans
        (fromRawPreservesAddition (validRawFraction a ha)
                                  (validRawFraction b hb))
        (cong₂ ℚ._+_ (rawToReduced a ha) (rawToReduced b hb))))
