module DASHI.Statistics.ZipfF13bSourcePNFIntegrationExact where

------------------------------------------------------------------------
-- F13b source-to-PNF FINAL CONSUMER; no duplicate rational or PNF.
--
-- Original OWNERS:
-- ZipfFamilyFiniteExact.finiteHurwitz and its denominator witnesses;
-- ZipfFractionFoldConditionalExact.concreteHurwitzSourceWritten;
-- ZipfPNFConstructiveNormalizationExact.inverseNormalizer,
-- zipfPNFAtoms and zipfPNFAtomsNormalize;
-- GenericExpectedFibreRateExact.ProbabilityAtom/probabilityTotal.
--
-- This module connects the previously written *raw source fraction*
-- identity to the existing *PNF normalized mass* at positive support.
-- This is an exact algebraic source-term proof, not a new empirical
-- Zipf law or a proof of analytic Hurwitz-zeta continuation.
-- Agda kernel TYPECHECK NOT EXECUTED; paid Boolean remains FALSE.
--
-- Classical normalization/rational proof roots: Agda stdlib authors,
-- finite probability; original Estoup/Zipf, Mandelbrot, Hurwitz.
-- Johl Brown-directed, OpenAI ChatGPT-assisted, 2026-10-28.
-- Existing original Ibrahim Monster 3B ownership retained.
-- No postulates, holes, unsafe termination or protected ESD changes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Rational.Base as ℚ

import DASHI.Statistics.ZipfFamilyFiniteExact as Finite
import DASHI.Statistics.ZipfFractionFoldConditionalExact as Fold
import DASHI.Statistics.ZipfPNFConstructiveNormalizationExact as PNF
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected

-- Rank support is positive by CONSTRUCTOR, not by an arbitrary
-- nonzero-count assumption or an independently supplied mock PMF.
-- The Finite.*NonZero proof is the ORIGINAL source constructor witness.

sourceFiniteHurwitz : (n shift exponent : Nat) → ℚ.ℚ
sourceFiniteHurwitz n shift exponent =
  Fold.concreteInterpret
    (Finite.finiteHurwitz (suc n) shift exponent)
    (Finite.finiteHurwitzDenominatorNonZero (suc n) shift exponent)

-- The source normalizer is identically the previous PNF rawSum.
-- This is a use of F13b, not a NEW normalization axiomatization.
sourceFiniteHurwitzEqualsRawSum : ∀ n shift exponent →
  sourceFiniteHurwitz n shift exponent ≡
    PNF.rawSum (suc n) shift exponent
sourceFiniteHurwitzEqualsRawSum n shift exponent =
  Fold.concreteHurwitzSourceWritten (suc n) shift exponent

-- Exact raw source total × the EXISTING positive inverse normalizer
-- agrees with the ALREADY-OWNED atom total. No second probability
-- object, no new law of rationals, and no identifying Boolean.
sourceScaledTotalEqualsPNFTotal : ∀ n shift exponent →
  ℚ._*_ (sourceFiniteHurwitz n shift exponent)
         (PNF.inverseNormalizer n shift exponent)
  ≡
  Expected.probabilityTotal (PNF.zipfPNFAtoms n shift exponent)
sourceScaledTotalEqualsPNFTotal n shift exponent =
  trans
    (cong
      (λ q → ℚ._*_ q (PNF.inverseNormalizer n shift exponent))
      (sourceFiniteHurwitzEqualsRawSum n shift exponent))
    (trans
      (sym
        (PNF.scaledSumFactors (suc n) shift exponent
          (PNF.inverseNormalizer n shift exponent)))
      (sym
        (PNF.atomsTotalEqualsScaledSum (suc n) shift exponent
          (PNF.inverseNormalizer n shift exponent)
          (PNF.inverseNormalizerPositive n shift exponent))))

-- Final F13b target: the SOURCE finite-Hurwitz fraction itself, after
-- scaling with the EXISTING PNF factor, normalizes exactly to one.
-- The proof finishes with the ORIGINAL zipfPNFAtomsNormalize theorem.
sourceFiniteHurwitzScaledToOne : ∀ n shift exponent →
  ℚ._*_ (sourceFiniteHurwitz n shift exponent)
         (PNF.inverseNormalizer n shift exponent) ≡ ℚ.1ℚ
sourceFiniteHurwitzScaledToOne n shift exponent =
  trans
    (sourceScaledTotalEqualsPNFTotal n shift exponent)
    (PNF.zipfPNFAtomsNormalize n shift exponent)
