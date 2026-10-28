module DASHI.Statistics.ZipfFractionFoldConditionalExact where

-- F13b, 28 October 2026. A lawful positive-denominator fraction fold.
-- The source FiniteFraction carrier does NOT forbid denominator zero.
-- Do NOT state an addition-homomorphism over all raw FiniteFractions:
-- that would wrongly require a division interpretation at denominator 0.
-- Every interpretation below receives an explicit nonzero witness.
--
-- Reuses ZipfFamilyFiniteExact.sumFirstDenominatorNonZero and
-- Data.Nat.Properties.m*n≢0. The ONLY missing local algebraic payment is
-- the concrete addFraction rational interpretation homomorphism.
--
-- Original finite-sum/rational algebra belongs to classical mathematics
-- and the standard-library authors. Repository adapter: Johl Brown with
-- OpenAI ChatGPT assistance. Existing prior Ibrahim 3B ownership retained.
-- SOURCE-WRITTEN / Agda kernel NOT typechecked. No postulates/unsafe flags.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as Nat using (NonZero; nonZero)
import Data.Nat.Properties as NatP
open import Data.Rational.Base as R using (ℚ; 0ℚ; _+_; normalize)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)
import Data.Rational.Properties as ℚP

import DASHI.Statistics.ZipfFamilyFiniteExact as Finite
import DASHI.Statistics.ZipfPNFConstructiveNormalizationExact as Normal
import DASHI.Core.FiniteUniformProbabilityNormalizationExact as Fraction

-- Interpret ONLY fractions with proof of a nonzero denominator.
-- The explicit witness makes the domain condition inescapable.
record PositiveFractionInterpretation : Set₁ where
  field
    interpret :
      (a : Finite.Fraction) →
      Nat.NonZero (Fraction.denominator a) → ℚ
    zero-preserved :
      interpret Finite.zeroFraction Nat.nonZero ≡ 0ℚ
    addition-preserved :
      (a b : Finite.Fraction) →
      (a≢0 : Nat.NonZero (Fraction.denominator a)) →
      (b≢0 : Nat.NonZero (Fraction.denominator b)) →
      interpret (Finite.addFraction a b)
        (NatP.m*n≢0
          (Fraction.denominator a) (Fraction.denominator b)
          {{a≢0}} {{b≢0}})
      ≡ interpret a a≢0 + interpret b b≢0

open PositiveFractionInterpretation public

rationalFold :
  (I : PositiveFractionInterpretation)
  (f : Nat → Finite.Fraction) →
  ((r : Nat) → Nat.NonZero (Fraction.denominator (f r))) →
  Nat → ℚ
rationalFold I f nz zero = 0ℚ
rationalFold I f nz (suc n) =
  interpret I (f n) (nz n) + rationalFold I f nz n

-- The actual existing denominator-product proof, not a replacement.
-- This is the generic induction step of the fraction normalization cut.
finiteFractionFoldHomomorphism :
  (I : PositiveFractionInterpretation)
  (f : Nat → Finite.Fraction)
  (nz : (r : Nat) → Nat.NonZero (Fraction.denominator (f r)))
  (n : Nat) →
  interpret I (Finite.sumFirst f n)
    (Finite.sumFirstDenominatorNonZero f n nz)
  ≡ rationalFold I f nz n
finiteFractionFoldHomomorphism I f nz zero =
  zero-preserved I
finiteFractionFoldHomomorphism I f nz (suc n) =
  trans
    (addition-preserved I
      (Finite.sumFirst f n) (f n)
      (Finite.sumFirstDenominatorNonZero f n nz) (nz n))
    (trans
      (cong₂ _+_
        (finiteFractionFoldHomomorphism I f nz n)
        refl)
      (ℚP.+-comm
        (rationalFold I f nz n)
        (interpret I (f n) (nz n))))

-- One typed additional term-compatibility obligation. No instance of this
-- record is fabricated; source-written normalize equality is still unpaid.
record ZipfPositiveFractionInterpretation : Set₁ where
  field
    positiveInterpretation : PositiveFractionInterpretation
    rank-term-preserved : ∀ r shift exponent →
      interpret positiveInterpretation
        (Finite.finiteMandelbrotTerm r shift exponent)
        (Finite.mandelbrotDenominatorNonZero r shift exponent)
      ≡ Normal.rawTerm r shift exponent

open ZipfPositiveFractionInterpretation public

-- Full finite Hurwitz fold follows from the two concrete hypotheses.
-- This is conditional on the *valid denominator* addition homomorphism.
sourceHurwitzEqualsRationalFold :
  (I : ZipfPositiveFractionInterpretation)
  (count shift exponent : Nat) →
  interpret (positiveInterpretation I)
    (Finite.finiteHurwitz count shift exponent)
    (Finite.finiteHurwitzDenominatorNonZero count shift exponent)
  ≡ Normal.rawSum count shift exponent
sourceHurwitzEqualsRationalFold I zero shift exponent =
  zero-preserved (positiveInterpretation I)
sourceHurwitzEqualsRationalFold I (suc n) shift exponent =
  trans
    (addition-preserved (positiveInterpretation I)
      (Finite.finiteHurwitz n shift exponent)
      (Finite.finiteMandelbrotTerm n shift exponent)
      (Finite.finiteHurwitzDenominatorNonZero n shift exponent)
      (Finite.mandelbrotDenominatorNonZero n shift exponent))
    (trans
      (cong₂ _+_
        (sourceHurwitzEqualsRationalFold I n shift exponent)
        (rank-term-preserved I n shift exponent))
      (ℚP.+-comm
        (Normal.rawSum n shift exponent)
        (Normal.rawTerm n shift exponent)))


------------------------------------------------------------------------
-- F13b Pareto reduction: the *actual* quotient interpretation is fixed.
-- No global division is attempted on raw denominator-zero fractions.
-- The ZERO and TERM laws are concrete. Only cross-denominator addition
-- compatibility remains as a separately typed mathematical obligation.
------------------------------------------------------------------------

concreteInterpret :
  (a : Finite.Fraction) →
  Nat.NonZero (Fraction.denominator a) → ℚ
concreteInterpret a denominatorNonZero =
  R.normalize (Fraction.numerator a) (Fraction.denominator a)
    {{denominatorNonZero}}

concreteZeroPreserved :
  concreteInterpret Finite.zeroFraction Nat.nonZero ≡ 0ℚ
concreteZeroPreserved = refl

-- The source's unreduced per-rank numerator/denominator is exactly
-- (1, mandelbrotDenominator r shift exponent).
concreteRankTermPreserved : ∀ r shift exponent →
  concreteInterpret
    (Finite.finiteMandelbrotTerm r shift exponent)
    (Finite.mandelbrotDenominatorNonZero r shift exponent)
  ≡ Normal.rawTerm r shift exponent
concreteRankTermPreserved r shift exponent =
  sym (Normal.rawTermMatchesSource r shift exponent)

-- This is the SINGLE unpaid F13b equation. It has a constrained domain.
-- It is a type, not an axiom declaration, inhabitant, proof token or Bool.
ConcreteAddLaw : Set
ConcreteAddLaw =
  (a b : Finite.Fraction) →
  (a≢0 : Nat.NonZero (Fraction.denominator a)) →
  (b≢0 : Nat.NonZero (Fraction.denominator b)) →
  concreteInterpret (Finite.addFraction a b)
    (NatP.m*n≢0
      (Fraction.denominator a) (Fraction.denominator b)
      {{a≢0}} {{b≢0}})
  ≡ concreteInterpret a a≢0 + concreteInterpret b b≢0

concreteFractionInterpretation :
  ConcreteAddLaw → PositiveFractionInterpretation
concreteFractionInterpretation addLaw = record
  { interpret = concreteInterpret
  ; zero-preserved = concreteZeroPreserved
  ; addition-preserved = addLaw
  }

concreteZipfInterpretation :
  ConcreteAddLaw → ZipfPositiveFractionInterpretation
concreteZipfInterpretation addLaw = record
  { positiveInterpretation = concreteFractionInterpretation addLaw
  ; rank-term-preserved = concreteRankTermPreserved
  }

-- All earlier fold work can now be consumed by providing JUST the
-- concrete cross-denominator addition theorem. This is deliberately
-- conditional and never registered as an unconditional paid F13b.
concreteSourceHurwitzEqualsRationalFold :
  (addLaw : ConcreteAddLaw)
  (count shift exponent : Nat) →
  concreteInterpret
    (Finite.finiteHurwitz count shift exponent)
    (Finite.finiteHurwitzDenominatorNonZero count shift exponent)
  ≡ Normal.rawSum count shift exponent
concreteSourceHurwitzEqualsRationalFold addLaw count shift exponent =
  sourceHurwitzEqualsRationalFold
    (concreteZipfInterpretation addLaw)
    count shift exponent
