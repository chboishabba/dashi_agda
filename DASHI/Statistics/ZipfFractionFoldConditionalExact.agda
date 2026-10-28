module DASHI.Statistics.ZipfFractionFoldConditionalExact where

-- 2026-10-28. F13b universal fold theorem.
-- Reuses ZipfFamilyFiniteExact and existing rational algebra.
-- NO postulates, unsafe flags, or fake Bool validation.
--
-- This file proves: zero/add/term preservation IMPLIES whole-fold
-- preservation. It does NOT assert the concrete normalized rational
-- interpretation of the unreduced source FiniteFraction has already
-- discharged the addition preservation premise.
--
-- Classical finite-fold homomorphism mathematics: no originality claim.
-- Source formulation: Johl Brown-directed with ChatGPT assistance.
-- Existing original Zipf/Estoup/Mandelbrot/Hurwitz and PNF owners retain
-- priority; unrelated Ibrahim Monster 3B owner is not imported.
-- Source-written, Agda kernel typecheck NOT YET EXECUTED.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)
import Data.Rational.Properties as ℚP

import DASHI.Statistics.ZipfFamilyFiniteExact as Finite
import DASHI.Statistics.ZipfPNFConstructiveNormalizationExact as Normal

-- The explicit assumptions are lawful morphism obligations, NOT proofs
-- of the actual `normalize numerator denominator` computation.
-- The instance is taken as an argument and cannot be synthesized from
-- the source-written repository code.

record FractionInterpretation : Set₁ where
  field
    interpret : Finite.Fraction → ℚ
    zero-preserved : interpret Finite.zeroFraction ≡ 0ℚ
    addition-preserved :
      (a b : Finite.Fraction) →
      interpret (Finite.addFraction a b) ≡ interpret a + interpret b

open FractionInterpretation public

-- Works for arbitrary finite fraction inputs. This is stronger than
-- the Zipf-only fold needed for source-normalizer parity.
finiteFractionFoldHomomorphism :
  (I : FractionInterpretation)
  (f : Nat → Finite.Fraction)
  (n : Nat) →
  interpret I (Finite.sumFirst f n) ≡
    rationalFold I f n
  where
    rationalFold : (I : FractionInterpretation)
      (f : Nat → Finite.Fraction) (n : Nat) → ℚ
    rationalFold I f zero = 0ℚ
    rationalFold I f (suc n) =
      interpret I (f n) + rationalFold I f n
finiteFractionFoldHomomorphism I f zero = zero-preserved I
finiteFractionFoldHomomorphism I f (suc n) =
  trans
    (addition-preserved I (Finite.sumFirst f n) (f n))
    (trans
      (cong₂ _+_
        (finiteFractionFoldHomomorphism I f n)
        refl)
      (ℚP.+-comm
        (rationalFold I f n)
        (interpret I (f n))))
  where
    rationalFold : (I : FractionInterpretation)
      (f : Nat → Finite.Fraction) (n : Nat) → ℚ
    rationalFold I f zero = 0ℚ
    rationalFold I f (suc n) =
      interpret I (f n) + rationalFold I f n

-- A direct Zipf owner term-preservation hypothesis is separately typed.
-- It must be established on the actual positive-normalized interpretation,
-- not supplied as a synthetic receipt or source Boolean.

record ZipfFractionInterpretation : Set₁ where
  field
    fractionInterpretation : FractionInterpretation
    term-preserved : ∀ r shift exponent →
      interpret fractionInterpretation
        (Finite.finiteMandelbrotTerm r shift exponent)
      ≡ Normal.rawTerm r shift exponent

open ZipfFractionInterpretation public

-- The conclusion is exactly the unpaid bridge identified in F13b.
-- No claim is made that ZipfFractionInterpretation has an inhabitant.

sourceHurwitzEqualsRationalFold :
  (I : ZipfFractionInterpretation) (count shift exponent : Nat) →
  interpret (fractionInterpretation I)
    (Finite.finiteHurwitz count shift exponent)
  ≡ Normal.rawSum count shift exponent
sourceHurwitzEqualsRationalFold I zero shift exponent =
  zero-preserved (fractionInterpretation I)
sourceHurwitzEqualsRationalFold I (suc n) shift exponent =
  trans
    (addition-preserved (fractionInterpretation I)
      (Finite.finiteHurwitz n shift exponent)
      (Finite.finiteMandelbrotTerm n shift exponent))
    (trans
      (cong₂ _+_
        (sourceHurwitzEqualsRationalFold I n shift exponent)
        (term-preserved I n shift exponent))
      (ℚP.+-comm
        (Normal.rawSum n shift exponent)
        (Normal.rawTerm n shift exponent)))
