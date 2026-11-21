module DASHI.Mathematics.Arithmetic.EllipticBSDOriginalLevel32SameCurveP0BIDIExact where

------------------------------------------------------------------------
-- BSD P0 SAME-OBJECT / NORMALIZED-COEFFICIENT BIDI.
--
-- Original selected curve is E : y^2 = x^3 - x (conductor 32,
-- CM by Z[i]); this module consumes, but does not alter, the
-- original typed BSD L-data, checked E(F_5) Frobenius row,
-- and K4 level-32 normalized one-dimensional q-series compiler.
--
-- A DIFFERENT j=0 CM curve y^2=x^3+1 (conductor 36, CM Z[omega])
-- is studied by dashi_lean4 #114.  Its coefficient a=0 must not be
-- identified definitionally with this BSD curve's coefficient a=-1.
-- Distinct Weierstrass coefficients alone are not an isomorphism
-- classification; this lemma is deliberately only a same-model veto.
--
-- Actual Newman/Ligozat analytic modularity, genuine genus/dimension
-- theorem, original modular-form coefficient instantiation, actual
-- complex eta, Mellin L(E,1), Mordell-Weil and Sha remain OPEN.
-- This source is a FINITE ALGEBRAIC weld, not the analytic K4 endpoint
-- or universal BSD. Agda kernel acceptance has not been run.
--
-- Original owners: BirchSwinnertonDyerBoundary;
-- EllipticCurveFrobeniusExact;
-- EllipticCMNormalizedOneDimensionalQSeriesExact;
-- EllipticCMLevel32EtaNewmanArithmeticExact;
-- EllipticCMLevel32GenusOneArithmeticExact.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Curve
import DASHI.Mathematics.Arithmetic.BirchSwinnertonDyerBoundary as BSD
import DASHI.Mathematics.Automorphic.EllipticCMNormalizedOneDimensionalQSeriesExact as Normalized
import DASHI.Mathematics.Automorphic.EllipticCMLevel32EtaNewmanArithmeticExact as Eta
import DASHI.Mathematics.Automorphic.EllipticCMLevel32GenusOneArithmeticExact as Genus

-- Identical to the original BSD source curve, NOT a second curve record.
originalSelectedCurve :
  Curve.ShortWeierstrassCurve
originalSelectedCurve = Curve.curveY2EqualsX3MinusX

originalSelectedCurveCoefficient :
  Curve.aCoefficient originalSelectedCurve ≡ - 1ℚ
originalSelectedCurveCoefficient = refl

-- A source claiming the same literal short Weierstrass model has
-- a=0 would contradict the ORIGINAL a=-1 coefficient.
originalSelectedCurveIsNotJZeroModel :
  Curve.aCoefficient originalSelectedCurve ≡ 0ℚ → ⊥
originalSelectedCurveIsNotJZeroModel ()

-- This existing original owner proves a *forward* implication:
-- genuine dimension-one proportionality + both q^1 normalizations
-- implies coefficient equality for every n.  We now construct the
-- exact reverse implication, without inventing a modularity source.
normalizedAllNBuildsOneDimensionalReceipt :
  ∀ {f g : Nat → ℚ} →
  f 1 ≡ 1ℚ → g 1 ≡ 1ℚ →
  ((n : Nat) → f n ≡ g n) →
  Normalized.NormalizedOneDimensionalQSeries f g
normalizedAllNBuildsOneDimensionalReceipt {g = g} fOne gOne allN =
  record
    { proportionalityScalar = 1ℚ
    ; genuineDimensionOneProportionality = λ n →
        trans (allN n) (sym (solve (g n ∷ [])))
    ; originalNormalizedFirstCoefficient = fOne
    ; etaNormalizedFirstCoefficient = gOne
    }

-- The SOURCE-TYPED original BSD local L-data must be indexed by
-- the exact E:y^2=x^3-x; its p=5 Frobenius must equal the ORIGINAL
-- checked point-count datum. No j=0 or unspecified-curve L-data
-- can inhabit this interface by definitional unification.
record OriginalSelectedLevel32K4P0
    (ellipticCoefficients etaCoefficients : Nat → ℚ) : Setω where
  field
    originalEllipticL :
      BSD.EllipticLFunctionData originalSelectedCurve
    originalP5Source :
      BSD.localFrobenius originalEllipticL 5
      ≡ Curve.p5FrobeniusDatum
    originalNormalizedDimensionOne :
      Normalized.NormalizedOneDimensionalQSeries
        ellipticCoefficients etaCoefficients

open OriginalSelectedLevel32K4P0 public

-- Once a GENUINE dimension-one modularity receipt is present,
-- every coefficient follows on the SAME selected BSD curve.
-- The statement does not synthesize the missing modularity receipt.
originalSelectedLevel32AllNCoefficientsAgree :
  ∀ {f g : Nat → ℚ}
    (source : OriginalSelectedLevel32K4P0 f g)
    (n : Nat) →
  f n ≡ g n
originalSelectedLevel32AllNCoefficientsAgree source n =
  Normalized.normalizedOneDimensionalAllNCoefficientsAgree
    (originalNormalizedDimensionOne source) n

-- Exact original level-32 finite arithmetic is already owned.
-- Retain the pre-existing certificates without constructing new
-- eta transformations, Eisenstein characters, or modular curve data.
originalLevel32NewmanAndGenusFinitePreflight :
  Eta.etaWeightedExponentSum ≡ 24
originalLevel32NewmanAndGenusFinitePreflight =
  Eta.etaLeadingExponentIsTwentyFour

originalLevel32GenusFinitePreflight :
  Genus.level32GenusOneNumber ≡ 1
originalLevel32GenusFinitePreflight = refl
